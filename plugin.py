# plugin.py
"""
JM 本子下载插件

支持 JM 搜索、章节下载、PDF/AES ZIP、NapCat 上传和以图搜本。
作者：氢
项目：https://github.com/hydrogen-francium/maibot_jm_plugin
"""
from __future__ import annotations

import asyncio
import base64
import difflib
import hashlib
import io
import ipaddress
import logging
import mimetypes
import os
import re
import shutil
import socket
import time
import unicodedata
import uuid
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Dict, List, Literal, Optional, Protocol, Tuple
from urllib.parse import urljoin, urlparse

import aiohttp

try:
    import pyzipper
    HAS_PYZIPPER = True
except ImportError:
    HAS_PYZIPPER = False

from PIL import Image
from maibot_sdk import Command, Field, MaiBotPlugin, PluginConfigBase
from maibot_sdk.compat.base import BaseCommand



# =============================================================================
# 工具函数
# =============================================================================

def sanitize_filename(name: str) -> str:
    """将文件名中的非法字符替换为下划线。

    替换 Windows 文件名非法字符和换行符。

    Args:
        name: 原始文件名

    Returns:
        处理后的安全文件名
    """
    return re.sub(r'[\\/:*?"<>|\r\n]+', '_', name).strip()


def sanitize_upload_filename(filename: str, max_bytes: int = 180) -> str:
    """限制对外文件名的 UTF-8 字节数，避免 QQ 拒绝超长名称。"""
    safe_name = sanitize_filename(Path(filename).name).rstrip(" .") or "jm_file"
    encoded = safe_name.encode("utf-8")
    if len(encoded) <= max_bytes:
        return safe_name

    suffix = Path(safe_name).suffix
    stem = safe_name[:-len(suffix)] if suffix else safe_name
    digest = hashlib.sha256(encoded).hexdigest()[:8]
    reserved = len(f"_{digest}{suffix}".encode("utf-8"))
    stem_budget = max(1, max_bytes - reserved)
    truncated = bytearray()
    for char in stem:
        char_bytes = char.encode("utf-8")
        if len(truncated) + len(char_bytes) > stem_budget:
            break
        truncated.extend(char_bytes)
    short_stem = truncated.decode("utf-8") or "jm_file"
    return f"{short_stem}_{digest}{suffix}"


def build_artifact_name(
    album_id: Any,
    chapter_index: Optional[int] = None,
    chapter_range: Optional[Tuple[int, int]] = None,
    only_first_chapter: bool = False,
) -> str:
    """生成稳定且短的对外文件名，避免标题字符触发 QQ 上传失败。"""
    normalized_id = re.sub(r"\D+", "", str(album_id or ""))
    artifact_name = f"JM{normalized_id}" if normalized_id else "JM_download"
    if chapter_range is not None:
        start_chapter, end_chapter = chapter_range
        if start_chapter == end_chapter:
            return f"{artifact_name}_{start_chapter:02d}"
        return f"{artifact_name}_{start_chapter:02d}-{end_chapter:02d}"
    if chapter_index is not None:
        return f"{artifact_name}_{chapter_index:02d}"
    if only_first_chapter:
        return f"{artifact_name}_01"
    return artifact_name


def sanitize_fake_extension(value: str) -> str:
    """限制伪装扩展名为单一文件名后缀，避免路径穿越。"""
    if re.fullmatch(r"\.[A-Za-z0-9_-]{1,16}", value or ""):
        return value
    return ".dat"



def _validate_remote_image_host(hostname: str) -> None:
    try:
        addresses = {ipaddress.ip_address(hostname)}
    except ValueError:
        try:
            addresses = {
                ipaddress.ip_address(info[4][0])
                for info in socket.getaddrinfo(hostname, None, type=socket.SOCK_STREAM)
            }
        except socket.gaierror as exc:
            raise ValueError("图片 URL 主机名无法解析") from exc
    if not addresses or any(
        address.is_private
        or address.is_loopback
        or address.is_link_local
        or address.is_multicast
        or address.is_reserved
        or address.is_unspecified
        for address in addresses
    ):
        raise ValueError("图片 URL 不允许访问内网或保留地址")


def _validate_image_url(value: str) -> str:
    url = _validate_http_url(value, "图片 URL")
    parsed = urlparse(url)
    assert parsed.hostname is not None
    _validate_remote_image_host(parsed.hostname)
    return url


def _natural_path_key(path: Path) -> Tuple[Any, ...]:
    return tuple(
        int(part) if part.isdigit() else part.casefold()
        for part in re.split(r"(\d+)", path.as_posix())
    )


def images_to_pdf_sync(image_paths: List[Path], output_pdf_path: str) -> str:
    """按顺序将图片合并为单个 PDF。

    - 所有图片统一转换为 RGB 模式。
    - 自动创建输出目录（若不存在）。

    Args:
        image_paths: 图片文件路径列表
        output_pdf_path: 输出 PDF 文件路径

    Returns:
        生成的 PDF 文件路径

    Raises:
        ValueError: 当没有图片提供时
    """
    if not image_paths:
        raise ValueError("没有图片可合并")

    images: List[Image.Image] = []
    # 使用上下文管理器确保文件句柄及时释放
    for img_path in image_paths:
        with Image.open(img_path) as im:
            img = im.convert("RGB") if im.mode != "RGB" else im.copy()
        images.append(img)

    os.makedirs(os.path.dirname(output_pdf_path) or ".", exist_ok=True)

    first_image = images[0]
    remaining_images = images[1:]
    first_image.save(output_pdf_path, save_all=True, append_images=remaining_images)

    for img in images:
        try:
            img.close()
        except Exception:
            pass

    return output_pdf_path



def pdf_to_encrypted_zip(pdf_path: str, zip_path: str, password: str) -> str:
    """将 PDF 文件转换为加密的 ZIP 压缩包（使用 pyzipper）。

    Args:
        pdf_path: PDF 文件路径
        zip_path: 输出的 ZIP 文件路径
        password: 压缩包密码

    Returns:
        生成的 ZIP 文件路径

    Raises:
        FileNotFoundError: 当 PDF 文件不存在时
        Exception: 压缩失败时
    """
    if not os.path.exists(pdf_path):
        raise FileNotFoundError(f"PDF 文件不存在: {pdf_path}")

    os.makedirs(os.path.dirname(zip_path) or ".", exist_ok=True)

    pdf_filename = os.path.basename(pdf_path)

    if not HAS_PYZIPPER:
        raise RuntimeError("加密 ZIP 功能需要安装 pyzipper，已取消生成以避免产生未加密文件")

    try:
        with pyzipper.AESZipFile(
            zip_path,
            "w",
            compression=pyzipper.ZIP_DEFLATED,
            encryption=pyzipper.WZ_AES,
        ) as zf:
            zf.setpassword(password.encode("utf-8"))
            zf.write(pdf_path, arcname=pdf_filename)
        return zip_path
    except Exception as e:
        raise RuntimeError(f"压缩失败: {e}") from e



# =============================================================================
# Napcat API 交互
# =============================================================================

def _napcat_payload_succeeded(payload: Dict[str, Any]) -> bool:
    """判断 Napcat JSON 响应是否明确表示业务成功。"""
    status = payload.get("status")
    if status is not None and str(status).lower() not in {"ok", "success", "succeeded"}:
        return False
    retcode = payload.get("retcode")
    if retcode is not None:
        try:
            return int(retcode) == 0
        except (TypeError, ValueError):
            return False
    data = payload.get("data")
    if isinstance(data, dict) and data.get("success") is False:
        return False
    return True


async def upload_pdf_via_napcat(
    pdf_path: str,
    filename: str,
    scope: str,
    target_id: int,
    napcat_base: str,
    timeout: int = 60,
    session: Optional[aiohttp.ClientSession] = None,
    content_type: Optional[str] = None,
) -> Tuple[bool, str]:
    """通过 Napcat API 上传 PDF 文件。

    尝试两种方式上传：
    1) JSON：传本地文件路径；失败则回退
    2) FormData：上传二进制内容

    Args:
        pdf_path: PDF 文件本地路径
        filename: 上传时的文件名
        scope: "group" 群聊 或 "private" 私聊
        target_id: 群号或用户 ID
        napcat_base: Napcat API 基础 URL
        timeout: 请求总超时（秒）

    Returns:
        (是否成功, 响应文本或错误信息)
    """
    napcat_base = _validate_http_url(napcat_base, "jm.napcat_base_url")
    filename = sanitize_upload_filename(filename)
    if scope not in {"group", "private"}:
        return False, "上传目标类型无效"
    if target_id <= 0:
        return False, "上传目标无效"
    if not Path(pdf_path).is_file():
        return False, "上传文件不存在"

    if content_type is None:
        content_type = mimetypes.guess_type(filename)[0] or "application/octet-stream"

    if scope == "group":
        url = f"{napcat_base}/upload_group_file"
        json_payload = {"group_id": target_id, "file": pdf_path, "name": filename}
    else:
        url = f"{napcat_base}/upload_private_file"
        json_payload = {"user_id": target_id, "file": pdf_path, "name": filename}

    request_timeout = aiohttp.ClientTimeout(total=timeout)
    owns_session = session is None
    if session is None:
        session = aiohttp.ClientSession(timeout=request_timeout)
    try:
        try:
            async with session.post(
                url,
                json=json_payload,
                timeout=request_timeout,
            ) as response:
                response_text = await response.text()
                if 200 <= response.status < 300:
                    try:
                        payload = await response.json(content_type=None)
                    except (aiohttp.ContentTypeError, ValueError):
                        payload = None
                    if isinstance(payload, dict) and _napcat_payload_succeeded(payload):
                        return True, response_text
        except aiohttp.ServerDisconnectedError:
            # NapCat 可能已经把请求交给 QQ 后才断开连接；盲目重试可能重复上传。
            return False, "Napcat 上传连接被服务端中断（请检查 Napcat 的上传错误日志）"
        except aiohttp.ClientError:
            pass

        form = aiohttp.FormData()
        if scope == "group":
            form.add_field("group_id", str(target_id))
        else:
            form.add_field("user_id", str(target_id))
        form.add_field("name", filename)
        with open(pdf_path, "rb") as file_handle:
            form.add_field("file", file_handle, filename=filename, content_type=content_type)
            async with session.post(
                url,
                data=form,
                timeout=request_timeout,
            ) as response:
                response_text = await response.text()
                if 200 <= response.status < 300:
                    try:
                        payload = await response.json(content_type=None)
                    except (aiohttp.ContentTypeError, ValueError):
                        payload = None
                    if isinstance(payload, dict) and _napcat_payload_succeeded(payload):
                        return True, response_text
                    return False, "Napcat 业务响应失败"
                return False, f"HTTP {response.status}"
    except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
        return False, f"Napcat 请求失败: {type(exc).__name__}"
    finally:
        if owns_session:
            await session.close()



# =============================================================================
# 搜图与图片提取相关
# =============================================================================

def _strip_base64_prefix(raw: str) -> str:
    value = str(raw or "").strip()
    if value.startswith("base64://"):
        return value[len("base64://") :].strip()
    if value.startswith("data:") and ";base64," in value:
        return value.split(";base64,", 1)[1].strip()
    return value


def _looks_like_base64(raw: str) -> bool:
    value = str(raw or "").strip()
    if not value or value.startswith(("http://", "https://", "file://", "/")):
        return False
    if value.startswith("base64://") or (value.startswith("data:") and ";base64," in value):
        return True
    if "." in value and value.rsplit(".", 1)[-1].isalpha() and len(value.rsplit(".", 1)[-1]) <= 5:
        return False
    try:
        return bool(base64.b64decode("".join(value.split()), validate=True))
    except Exception:
        return False


def _find_image_in_segments(message_segments: Any, *, include_emoji: bool = False) -> Any:
    """从 Host/OneBot 消息段中递归提取图片的 base64 或 URL。"""
    if not isinstance(message_segments, list):
        return None
    accepted = {"image", "emoji"} if include_emoji else {"image"}
    for segment in message_segments:
        if not isinstance(segment, dict):
            continue
        segment_type = str(segment.get("type") or "").lower()
        data = segment.get("data")
        if segment_type in {"seglist", "forward"}:
            if segment_type == "forward" and isinstance(data, list):
                for node in data:
                    if isinstance(node, dict):
                        found = _find_image_in_segments(node.get("content"), include_emoji=include_emoji)
                        if found:
                            return found
            else:
                found = _find_image_in_segments(data, include_emoji=include_emoji)
                if found:
                    return found
            continue
        if segment_type not in accepted:
            continue

        top_level_binary = segment.get("binary_data_base64")
        if isinstance(top_level_binary, str) and _looks_like_base64(top_level_binary):
            return _strip_base64_prefix(top_level_binary)
        if isinstance(data, str):
            if _looks_like_base64(data):
                return _strip_base64_prefix(data)
            if data.startswith(("http://", "https://")):
                return data
        if isinstance(data, dict):
            for key in ("binary_data_base64", "base64", "data"):
                candidate = data.get(key)
                if isinstance(candidate, str) and _looks_like_base64(candidate):
                    return _strip_base64_prefix(candidate)
            url = str(data.get("url") or data.get("src") or "").strip()
            if url.startswith(("http://", "https://")):
                return url
    return None


def _extract_message_image(message: Any) -> Any:
    if not isinstance(message, dict):
        return None
    for key in ("raw_message", "message_segment", "message_segments", "segments"):
        found = _find_image_in_segments(message.get(key))
        if found:
            return found
    direct = message.get("image_data") or message.get("image")
    if direct:
        return direct
    # SDK 消息能力返回 {success, message}，部分适配器还会再包一层 data。
    for key in ("message", "data"):
        nested = message.get(key)
        if nested is message:
            continue
        found = _extract_message_image(nested)
        if found:
            return found
    return None


def _find_reply_target_id(message: Any) -> str:
    if not isinstance(message, dict):
        return ""
    direct = str(message.get("reply_to") or "").strip()
    if direct:
        return direct
    segments = message.get("raw_message")
    if not isinstance(segments, list):
        return ""
    for segment in segments:
        if not isinstance(segment, dict) or str(segment.get("type") or "").lower() != "reply":
            continue
        data = segment.get("data")
        if isinstance(data, dict):
            for key in ("target_message_id", "id", "message_id"):
                value = str(data.get(key) or "").strip()
                if value:
                    return value
        else:
            value = str(data or "").strip()
            if value:
                return value
    return ""


def _adapter_message_nodes(result: Any) -> List[Any]:
    nodes = [result]
    if isinstance(result, dict):
        nodes.extend((result.get("message"), result.get("data")))
        if isinstance(result.get("data"), dict):
            nodes.append(result["data"].get("message"))
    return nodes


@dataclass(frozen=True)
class AdapterImageSource:
    data: bytes
    filename: str
    mime_type: str


async def _download_adapter_image(
    url: str,
    session: aiohttp.ClientSession,
    max_bytes: int,
) -> AdapterImageSource:
    """读取适配器返回的图片 URL；该 URL 允许指向本机，但禁止跨主机重定向。"""
    if session is None or session.closed:
        raise RuntimeError("搜图 HTTP 会话尚未初始化")
    parsed = urlparse(str(url or "").strip())
    if parsed.scheme not in {"http", "https"} or not parsed.hostname:
        raise ValueError("适配器返回了无效的图片 URL")
    origin = (parsed.scheme, parsed.hostname, parsed.port)
    current_url = parsed.geturl()
    for redirect_count in range(4):
        async with session.get(current_url, allow_redirects=False) as response:
            if response.status in {301, 302, 303, 307, 308}:
                location = response.headers.get("Location")
                if not location or redirect_count >= 3:
                    raise RuntimeError("适配器图片重定向无效或次数过多")
                next_url = urljoin(current_url, location)
                next_parsed = urlparse(next_url)
                if (next_parsed.scheme, next_parsed.hostname, next_parsed.port) != origin:
                    raise ValueError("适配器图片不允许重定向到其他主机")
                current_url = next_url
                continue
            if response.status >= 400:
                raise RuntimeError(f"读取适配器图片返回 HTTP {response.status}")
            if response.content_length is not None and response.content_length > max_bytes:
                raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
            chunks: List[bytes] = []
            total = 0
            async for chunk in response.content.iter_chunked(64 * 1024):
                total += len(chunk)
                if total > max_bytes:
                    raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
                chunks.append(chunk)
            image = b"".join(chunks)
            if not image:
                raise ValueError("适配器返回的图片内容为空")
            content_type = response.headers.get("Content-Type", "").split(";", 1)[0].strip()
            current_path = urlparse(current_url).path
            filename = sanitize_filename(Path(current_path).name) or "image.bin"
            mime_type = (
                content_type
                or mimetypes.guess_type(filename)[0]
                or "application/octet-stream"
            )
            if filename == "image.bin":
                filename = f"image{mimetypes.guess_extension(mime_type) or '.bin'}"
            return AdapterImageSource(image, filename, mime_type)
    raise RuntimeError("适配器图片重定向次数过多")


async def _resolve_adapter_image(
    message_id: str,
    ctx: Any,
    session: Optional[aiohttp.ClientSession] = None,
    max_bytes: int = 10 * 1024 * 1024,
) -> Any:
    if not message_id or ctx is None or not hasattr(ctx, "api"):
        return None
    try:
        result = await ctx.api.call(
            "adapter.napcat.message.get_msg",
            message_id=message_id,
            timeout_ms=30_000,
        )
    except Exception:
        ctx.logger.debug("NapCat get_msg 取图失败", exc_info=True)
        return None
    for node in _adapter_message_nodes(result):
        found = _find_image_in_segments(node)
        if found:
            if isinstance(found, str) and found.startswith(("http://", "https://")):
                downloaded = await _download_adapter_image(found, session, max_bytes)
                if downloaded:
                    return downloaded
            else:
                return found
        if not isinstance(node, list):
            continue
        for segment in node:
            if not isinstance(segment, dict) or str(segment.get("type") or "").lower() != "image":
                continue
            data = segment.get("data")
            if not isinstance(data, dict):
                continue
            file_ref = str(data.get("file") or data.get("file_id") or "").strip()
            if not file_ref:
                continue
            try:
                image_info = await ctx.api.call(
                    "adapter.napcat.file.get_image",
                    file=file_ref,
                    timeout_ms=30_000,
                )
            except Exception:
                continue
            for info in _adapter_message_nodes(image_info):
                if isinstance(info, dict):
                    url = str(info.get("url") or "").strip()
                    if url:
                        return await _download_adapter_image(url, session, max_bytes)
    return None


async def _resolve_command_image(
    message: Any,
    ctx: Any,
    stream_id: str = "",
    session: Optional[aiohttp.ClientSession] = None,
    max_bytes: int = 10 * 1024 * 1024,
) -> Any:
    """解析当前图片或引用图片，不回退到群聊中的任意近期图片。"""
    if not isinstance(message, dict):
        return None
    resolved_stream_id = stream_id or str(message.get("session_id") or "")
    reply_id = _find_reply_target_id(message)
    if reply_id:
        try:
            quoted = await ctx.message.get_by_id(
                reply_id,
                stream_id=resolved_stream_id,
                include_binary_data=True,
            )
        except Exception:
            quoted = None
        found = _extract_message_image(quoted)
        if found:
            return found
        found = await _resolve_adapter_image(
            reply_id,
            ctx,
            session=session,
            max_bytes=max_bytes,
        )
        if found:
            return found

    message_id = str(message.get("message_id") or "").strip()
    if message_id:
        try:
            expanded = await ctx.message.get_by_id(
                message_id,
                stream_id=resolved_stream_id,
                include_binary_data=True,
            )
        except Exception:
            expanded = None
        found = _extract_message_image(expanded)
        if found:
            return found

    found = _extract_message_image(message)
    if found:
        return found
    if message_id:
        return await _resolve_adapter_image(
            message_id,
            ctx,
            session=session,
            max_bytes=max_bytes,
        )
    return None

@dataclass(frozen=True)
class ImageSearchResult:
    title: str
    similarity: float
    source: str = ""
    detail_url: str = ""
    page_url: str = ""


class ImageSearchProvider(Protocol):
    async def search(self, image: bytes, filename: str, mime_type: str) -> List[ImageSearchResult]: ...


class ImageAcquisitionError(RuntimeError):
    """命令消息中的图片无法读取或规范化。"""


class ImageProviderError(RuntimeError):
    """搜图 provider 的配置、网络或响应协议发生错误。"""


class ImageProviderTimeoutError(ImageProviderError):
    """搜图 provider 在限定时间内未返回响应。"""


def _validate_http_url(value: str, name: str) -> str:
    parsed = urlparse((value or "").strip())
    if parsed.scheme not in {"http", "https"} or not parsed.hostname:
        raise ValueError(f"{name} 必须是有效的 http/https URL")
    return value.rstrip("/")


def _soutubot_api_key(now_ts: int, user_agent: str, m_value: int) -> str:
    value = str(now_ts**2 + len(user_agent) ** 2 + m_value).encode("utf-8")
    return base64.b64encode(value).decode("ascii")[::-1].replace("=", "")


def _extract_soutubot_m(html: str) -> int:
    match = re.search(r"\bm\s*:\s*(\d+)", html)
    if match is None:
        raise RuntimeError("搜图服务首页结构已变化")
    return int(match.group(1))


_SOUTUBOT_SOURCE_HOSTS = {
    "nhentai": "nhentai.net",
    "ehentai": "e-hentai.org",
    "panda": "panda.chaika.moe",
}


def _normalize_soutubot_url(source: str, path: Any) -> str:
    value = str(path or "").strip()
    if not value:
        return ""
    if value.startswith(("http://", "https://")):
        return value
    host = _SOUTUBOT_SOURCE_HOSTS.get(source.lower(), "")
    return urljoin(f"https://{host}/", value.lstrip("/")) if host else value


class SoutuBotProvider:
    def __init__(self, config: SotuConfig, session: aiohttp.ClientSession):
        self.config = config
        self.session = session
        self.api_base = _validate_http_url(config.api_base, "sotu.api_base")

    async def _homepage_state(self) -> Tuple[int, str]:
        user_agent = self.config.user_agent
        headers = {"User-Agent": user_agent, "Accept": "text/html,application/xhtml+xml"}
        direct_error: Optional[Exception] = None
        try:
            async with self.session.get(
                f"{self.api_base}/",
                headers=headers,
                proxy=self.config.proxy or None,
            ) as response:
                html = await response.text()
                if response.status >= 400:
                    raise RuntimeError(f"搜图服务首页返回 HTTP {response.status}")
                return _extract_soutubot_m(html), user_agent
        except Exception as exc:
            direct_error = exc

        if not self.config.flaresolverr_url.strip():
            raise RuntimeError("搜图服务首页握手失败；可配置 sotu.flaresolverr_url 后重试") from direct_error

        flaresolverr_url = _validate_http_url(
            self.config.flaresolverr_url,
            "sotu.flaresolverr_url",
        )
        payload = {
            "cmd": "request.get",
            "url": f"{self.api_base}/",
            "maxTimeout": self.config.timeout_seconds * 1000,
        }
        async with self.session.post(f"{flaresolverr_url}/v1", json=payload) as response:
            if response.status >= 400:
                raise RuntimeError(f"FlareSolverr 返回 HTTP {response.status}")
            try:
                data = await response.json(content_type=None)
            except Exception as exc:
                raise RuntimeError("FlareSolverr 返回了非 JSON 响应") from exc

        solution = data.get("solution") if isinstance(data, dict) else None
        if not isinstance(solution, dict):
            raise RuntimeError("FlareSolverr 返回的数据结构无效")
        html = str(solution.get("response") or "")
        solved_user_agent = str(solution.get("userAgent") or "").strip() or user_agent
        cookies = solution.get("cookies")
        if isinstance(cookies, list):
            cookie_values = {
                str(cookie.get("name")): str(cookie.get("value"))
                for cookie in cookies
                if isinstance(cookie, dict) and cookie.get("name") and cookie.get("value") is not None
            }
            if cookie_values:
                self.session.cookie_jar.update_cookies(cookie_values)
        return _extract_soutubot_m(html), solved_user_agent

    async def search(self, image: bytes, filename: str, mime_type: str) -> List[ImageSearchResult]:
        m_value, user_agent = await self._homepage_state()

        headers = {
            "User-Agent": user_agent,
            "Accept": "application/json, text/plain, */*",
            "X-API-KEY": _soutubot_api_key(int(time.time()), user_agent, m_value),
            "X-Requested-With": "XMLHttpRequest",
            "Origin": self.api_base,
            "Referer": f"{self.api_base}/",
        }
        payload: Any = None
        for attempt in range(2):
            # aiohttp 的 multipart payload 可能在发送后被消费，重试必须重新构造。
            form = aiohttp.FormData()
            form.add_field("factor", str(self.config.factor))
            form.add_field("file", image, filename=filename, content_type=mime_type)
            try:
                async with self.session.post(
                    urljoin(f"{self.api_base}/", "api/search"),
                    data=form,
                    headers=headers,
                    proxy=self.config.proxy or None,
                ) as response:
                    if response.status >= 400:
                        detail = re.sub(r"\s+", " ", (await response.text()).strip())[:200]
                        suffix = f"：{detail}" if detail else ""
                        raise RuntimeError(f"搜图服务返回 HTTP {response.status}{suffix}")
                    try:
                        payload = await response.json(content_type=None)
                    except Exception as exc:
                        raise RuntimeError("搜图服务返回了非 JSON 响应") from exc
                break
            except asyncio.TimeoutError as exc:
                if attempt == 0:
                    continue
                raise ImageProviderTimeoutError(
                    f"SoutuBot 上传搜索请求超时（已重试 1 次，单次上限 {self.config.timeout_seconds} 秒）"
                ) from exc
            except aiohttp.ClientConnectionError as exc:
                if attempt == 0:
                    continue
                detail = str(exc).strip()
                suffix = f"：{detail}" if detail else ""
                raise ImageProviderError(
                    f"SoutuBot 搜索连接失败（已重试 1 次）{suffix}"
                ) from exc

        raw_results = payload.get("data") if isinstance(payload, dict) else None
        if not isinstance(raw_results, list):
            raise RuntimeError("搜图服务返回的数据结构无效")
        results: List[ImageSearchResult] = []
        for item in raw_results:
            if not isinstance(item, dict):
                continue
            try:
                similarity = float(item.get("similarity") or 0)
            except (TypeError, ValueError):
                similarity = 0.0
            title = str(item.get("title") or "").strip()
            if title and similarity >= self.config.min_similarity:
                source = str(item.get("source") or "").strip()
                results.append(
                    ImageSearchResult(
                        title=title,
                        similarity=similarity,
                        source=source,
                        detail_url=_normalize_soutubot_url(source, item.get("subjectPath")),
                        page_url=_normalize_soutubot_url(source, item.get("pagePath")),
                    )
                )
        results.sort(key=lambda result: result.similarity, reverse=True)
        return results[: self.config.max_results]


class SauceNaoProvider:
    def __init__(self, config: SotuConfig, session: aiohttp.ClientSession):
        if not config.api_key.strip():
            raise ValueError("使用 SauceNAO 时必须配置 sotu.api_key")
        self.config = config
        self.session = session

    async def search(self, image: bytes, filename: str, mime_type: str) -> List[ImageSearchResult]:
        form = aiohttp.FormData()
        form.add_field("file", image, filename=filename, content_type=mime_type)
        params = {"db": 999, "output_type": 2, "numres": self.config.max_results, "api_key": self.config.api_key}
        async with self.session.post(
            "https://saucenao.com/search.php",
            params=params,
            data=form,
            proxy=self.config.proxy or None,
        ) as response:
            if response.status >= 400:
                raise RuntimeError(f"SauceNAO 返回 HTTP {response.status}")
            try:
                payload = await response.json(content_type=None)
            except Exception as exc:
                raise RuntimeError("SauceNAO 返回了非 JSON 响应") from exc

        raw_results = payload.get("results") if isinstance(payload, dict) else None
        if not isinstance(raw_results, list):
            raise RuntimeError("SauceNAO 返回的数据结构无效")
        results: List[ImageSearchResult] = []
        for item in raw_results:
            if not isinstance(item, dict):
                continue
            header = item.get("header") if isinstance(item.get("header"), dict) else {}
            data = item.get("data") if isinstance(item.get("data"), dict) else {}
            try:
                similarity = float(header.get("similarity") or 0)
            except (TypeError, ValueError):
                similarity = 0.0
            title = str(data.get("title") or data.get("jp_name") or data.get("eng_name") or data.get("source") or "").strip()
            if title and similarity >= self.config.min_similarity:
                ext_urls = data.get("ext_urls") if isinstance(data.get("ext_urls"), list) else []
                results.append(
                    ImageSearchResult(
                        title=title,
                        similarity=similarity,
                        source=str(header.get("index_name") or "SauceNAO"),
                        detail_url=str(ext_urls[0]) if ext_urls else "",
                    )
                )
        results.sort(key=lambda result: result.similarity, reverse=True)
        return results[: self.config.max_results]


async def _read_image_source(
    source: Any,
    config: SotuConfig,
    session: aiohttp.ClientSession,
) -> Tuple[bytes, str, str]:
    """读取消息图片，并在解码或下载过程中执行大小限制。"""
    max_bytes = config.max_upload_bytes
    if isinstance(source, AdapterImageSource):
        image = source.data
        filename = source.filename
        mime_type = source.mime_type
    elif isinstance(source, dict):
        source = (
            source.get("base64")
            or source.get("url")
            or source.get("path")
            or source.get("file")
            or source.get("data")
        )
        return await _read_image_source(source, config, session)
    elif isinstance(source, bytes):
        image = source
        filename = "image.bin"
        mime_type = "application/octet-stream"
    elif isinstance(source, str):
        value = source.strip()
        if value.startswith("data:") and "," in value:
            header, value = value.split(",", 1)
            compact = "".join(value.split())
            if len(compact) > ((max_bytes + 2) // 3) * 4 + 4:
                raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
            padding = len(compact) - len(compact.rstrip("="))
            if len(compact) * 3 // 4 - padding > max_bytes:
                raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
            mime_type = header[5:].split(";", 1)[0] or "application/octet-stream"
            filename = f"image{mimetypes.guess_extension(mime_type) or '.bin'}"
            try:
                image = base64.b64decode(compact, validate=True)
            except Exception as exc:
                raise ValueError("图片 base64 数据无效") from exc
        elif value.startswith(("http://", "https://")):
            url = _validate_image_url(value)
            parsed = urlparse(url)
            filename = sanitize_filename(Path(parsed.path).name) or "image.bin"
            chunks: List[bytes] = []
            total = 0
            current_url = url
            for redirect_count in range(6):
                # 禁止 aiohttp 自动跟随重定向，确保每一跳都重新做 SSRF 校验。
                async with session.get(
                    current_url,
                    proxy=config.proxy or None,
                    allow_redirects=False,
                ) as response:
                    if response.status in {301, 302, 303, 307, 308}:
                        location = response.headers.get("Location")
                        if not location:
                            raise RuntimeError("图片重定向缺少目标地址")
                        if redirect_count >= 5:
                            raise RuntimeError("图片重定向次数过多")
                        current_url = _validate_image_url(
                            urljoin(current_url, location)
                        )
                        continue
                    if response.status >= 400:
                        raise RuntimeError(f"下载图片返回 HTTP {response.status}")
                    declared_size = response.content_length
                    if declared_size is not None and declared_size > max_bytes:
                        raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
                    async for chunk in response.content.iter_chunked(64 * 1024):
                        total += len(chunk)
                        if total > max_bytes:
                            raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
                        chunks.append(chunk)
                    image = b"".join(chunks)
                    mime_type = response.headers.get("Content-Type", "").split(";", 1)[0]
                    break
            else:
                raise RuntimeError("图片重定向次数过多")
            parsed = urlparse(current_url)
            filename = sanitize_filename(Path(parsed.path).name) or "image.bin"
            mime_type = mime_type or mimetypes.guess_type(filename)[0] or "application/octet-stream"
        else:
            compact = "".join(value.split())
            if len(compact) > ((max_bytes + 2) // 3) * 4 + 4:
                raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
            try:
                image = base64.b64decode(compact, validate=True)
            except Exception as exc:
                raise ValueError("图片来源必须是消息附件、base64 或受允许的远程图片 URL") from exc
            filename = "image.bin"
            mime_type = "application/octet-stream"
    else:
        raise ValueError("图片来源无法识别")

    if not image:
        raise ValueError("图片内容为空")
    if len(image) > max_bytes:
        raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
    return image, filename, mime_type


def _normalize_image_upload(
    image: bytes,
    filename: str,
    mime_type: str,
    max_bytes: int,
) -> Tuple[bytes, str, str]:
    """确保 multipart 文件名、MIME 和实际图片格式一致。"""
    try:
        with Image.open(io.BytesIO(image)) as opened:
            opened.verify()
            image_format = str(opened.format or "").upper()
    except Exception as exc:
        raise ValueError("图片内容不是受支持的图片格式") from exc

    format_info = {
        "JPEG": (".jpg", "image/jpeg"),
        "PNG": (".png", "image/png"),
        "GIF": (".gif", "image/gif"),
        "WEBP": (".webp", "image/webp"),
        "BMP": (".bmp", "image/bmp"),
    }
    if image_format not in format_info:
        raise ValueError(f"暂不支持该图片格式：{image_format or 'unknown'}")
    extension, detected_mime = format_info[image_format]
    safe_stem = sanitize_filename(Path(filename or "image").stem) or "image"
    normalized_filename = f"{safe_stem}{extension}"
    if len(image) > max_bytes:
        raise ValueError(f"图片超过大小限制（{max_bytes} bytes）")
    return image, normalized_filename, detected_mime


async def search_image(
    image_source: Any,
    config: SotuConfig,
    session: aiohttp.ClientSession,
) -> List[ImageSearchResult]:
    if session is None or session.closed:
        raise ImageProviderError("搜图 HTTP 会话尚未初始化")
    try:
        image, filename, mime_type = await _read_image_source(
            image_source,
            config,
            session,
        )
        image, filename, mime_type = _normalize_image_upload(
            image,
            filename,
            mime_type,
            config.max_upload_bytes,
        )
    except Exception as exc:
        raise ImageAcquisitionError(str(exc) or "图片读取失败") from exc

    try:
        provider: ImageSearchProvider
        if config.provider == "saucenao":
            provider = SauceNaoProvider(config, session)
        else:
            provider = SoutuBotProvider(config, session)
        return await provider.search(image, filename, mime_type)
    except ImageProviderError:
        raise
    except Exception as exc:
        raise ImageProviderError(str(exc) or "搜图服务调用失败") from exc


def _normalize_soutu_jm_keyword(title: str) -> str:
    """移除搜图标题中的发布标签、场次标记和章节号，生成 JM 搜索词。"""
    keyword = unicodedata.normalize("NFKC", str(title or "")).strip()
    keyword = re.sub(r"\[[^\]]*\]|【[^】]*】|［[^］]*］", " ", keyword)
    # C103、COMIC1☆22 等同人展场次不是作品名；保留普通的 (前编) 等标题内容。
    keyword = re.sub(
        r"\(\s*(?:C\d{2,4}|COMIC\s*1[^)]*|COMITIA\s*\d+|例大祭\s*\d+)\s*\)",
        " ",
        keyword,
        flags=re.IGNORECASE,
    )
    keyword = re.sub(r"\s*#\s*\d+(?:\.\d+)?\s*$", "", keyword)
    return re.sub(r"\s+", " ", keyword).strip()


def _soutu_jm_keyword_candidates(title: str) -> List[str]:
    """按搜图标题的双语部分生成 JM 候选词，避免单一语言搜不到。"""
    raw = str(title or "").strip()
    parts = re.split(r"\s*[|｜]\s*", raw)
    candidates: List[str] = []
    for part in parts:
        keyword = _normalize_soutu_jm_keyword(part)
        # 搜图 Bot 酱常在末尾附加来源/杂志元数据，不属于作品标题。
        keyword = re.sub(r"\s*\([^()]{1,80}\)\s*$", "", keyword).strip()
        keyword = re.sub(r"\s*#\s*\d+(?:\.\d+)?\s*$", "", keyword).strip()
        if keyword and keyword not in candidates:
            candidates.append(keyword)
    return candidates


def _title_comparison_key(title: str) -> str:
    """生成跨语言标题比较键，忽略发布元数据、大小写、空白和标点。"""
    value = _normalize_soutu_jm_keyword(title)
    value = re.sub(r"\s*\([^()]{1,80}\)\s*$", "", value).strip()
    return "".join(
        char.casefold()
        for char in unicodedata.normalize("NFKC", value)
        if char.isalnum()
    )


def _title_bigrams(value: str) -> set[str]:
    if len(value) < 2:
        return {value} if value else set()
    return {value[index : index + 2] for index in range(len(value) - 1)}


def _title_similarity(source_title: str, candidate_title: str) -> float:
    """按双语标题分段计算 0~1 相似度，供 JM 结果甄别。"""
    source_parts = _soutu_jm_keyword_candidates(source_title) or [source_title]
    candidate_parts = _soutu_jm_keyword_candidates(candidate_title) or [candidate_title]
    best_score = 0.0
    for source_part in source_parts:
        source_key = _title_comparison_key(source_part)
        if not source_key:
            continue
        for candidate_part in candidate_parts:
            candidate_key = _title_comparison_key(candidate_part)
            if not candidate_key:
                continue
            if source_key == candidate_key:
                return 1.0

            sequence_score = difflib.SequenceMatcher(
                None,
                source_key,
                candidate_key,
                autojunk=False,
            ).ratio()
            source_bigrams = _title_bigrams(source_key)
            candidate_bigrams = _title_bigrams(candidate_key)
            union_size = len(source_bigrams) + len(candidate_bigrams)
            dice_score = (
                2 * len(source_bigrams & candidate_bigrams) / union_size
                if union_size
                else 0.0
            )
            containment_score = 0.0
            shorter, longer = sorted(
                (source_key, candidate_key),
                key=len,
            )
            if len(shorter) >= 4 and shorter in longer:
                containment_score = 0.82 + 0.18 * (len(shorter) / len(longer))
            best_score = max(
                best_score,
                sequence_score,
                dice_score,
                containment_score,
            )
    return min(best_score, 1.0)


def _rank_jm_title_results(
    source_title: str,
    results: List[Dict[str, Any]],
) -> List[Tuple[float, Dict[str, Any]]]:
    ranked = [
        (_title_similarity(source_title, str(album.get("title") or "")), album)
        for album in results
    ]
    ranked.sort(key=lambda item: item[0], reverse=True)
    return ranked


def _is_accurate_title_match(
    source_title: str,
    candidate_title: str,
    score: float,
) -> bool:
    shortest = min(
        len(_title_comparison_key(source_title)),
        len(_title_comparison_key(candidate_title)),
    )
    threshold = 0.80 if shortest < 6 else 0.62
    return shortest >= 3 and score >= threshold


@dataclass(frozen=True)
class JmTitleMatch:
    image_result: ImageSearchResult
    keyword: str
    ranked_results: List[Tuple[float, Dict[str, Any]]]


async def _find_accurate_jm_match(
    image_results: List[ImageSearchResult],
    option: Any,
) -> Optional[JmTitleMatch]:
    """依次尝试前三条搜图结果，仅返回标题甄别通过的 JM 结果。"""
    for image_result in image_results[:3]:
        title = image_result.title
        keywords = _soutu_jm_keyword_candidates(title)
        for keyword in keywords:
            candidate_results = await search_jm_by_keyword(keyword, option)
            # JM 满页通常意味着关键词过宽，不能据此认定匹配成功。
            if not candidate_results or len(candidate_results) >= 80:
                continue
            ranked = _rank_jm_title_results(title, candidate_results)
            accurate = [
                item
                for item in ranked
                if _is_accurate_title_match(
                    title,
                    str(item[1].get("title") or ""),
                    item[0],
                )
            ]
            if accurate:
                return JmTitleMatch(
                    image_result=image_result,
                    keyword=keyword,
                    ranked_results=accurate,
                )
    return None


async def search_jm_by_keyword(keyword: str, option, page: int = 1) -> List[Dict]:
    """在 JMComic 中搜索关键字"""
    try:
        import jmcomic

        def _search():
            client = option.new_jm_client()
            return client.search_site(keyword, page=page)

        results = await asyncio.to_thread(_search)

        if not results:
            return []

        data = []
        if hasattr(results, 'content'):
            for album_id, album_info in results.content:
                if isinstance(album_info, dict):
                    title = album_info.get('name', album_info.get('title', '未知'))
                    author = album_info.get('author', '未知')
                    if isinstance(author, list):
                        author = ','.join(author)
                    likes = album_info.get('likes', '0')

                    data.append({
                        "id": album_id,
                        "title": title,
                        "author": author,
                        "likes": likes
                    })

        if not data:
            for album in results:
                if hasattr(album, 'album_id'):
                    data.append({
                        "id": album.album_id,
                        "title": album.title,
                        "author": getattr(album, 'author', '未知'),
                        "likes": getattr(album, 'likes', '0')
                    })
                elif isinstance(album, tuple) and len(album) >= 2:
                    data.append({
                        "id": album[0],
                        "title": album[1],
                        "author": '未知',
                        "likes": '0'
                    })

        return data
    except Exception:
        return []

# =============================================================================
# JMComic 下载功能
# =============================================================================

def _write_unique_option_file(output_dir: str, proxy: str = "", option_dir: Optional[str] = None) -> str:
    """生成唯一的 jmcomic option 文件，并将下载目录写入配置。"""
    os.makedirs(output_dir, exist_ok=True)
    option_root = option_dir or output_dir
    os.makedirs(option_root, exist_ok=True)
    option_file = os.path.join(option_root, f"option_{uuid.uuid4().hex}.yml")
    content = f"dir_rule:\n  rule: Bd/Aid/Pid\n  base_dir: {output_dir}\n"
    content += "download:\n  threading:\n    image: 5\n"
    if proxy:
        content += (
            "client:\n"
            "  postman:\n"
            "    meta_data:\n"
            "      proxies:\n"
            f"        http: {proxy}\n"
            f"        https: {proxy}\n"
        )
    with open(option_file, "w", encoding="utf-8") as f:
        f.write(content)
    return option_file


async def check_album_chapters(
    album_id: str,
    output_dir: str,
    option_dir: str,
    proxy: str = "",
) -> Tuple[bool, Optional[int], Optional[str]]:
    """检查本子的章节数量。

    初始化 jmcomic 配置后查询指定 ID 的章节信息。
    
    Args:
        album_id: 本子 ID
        output_dir: 自定义输出目录，为空时使用默认目录
    
    Returns:
        元组 (是否成功, 章节数量, 错误信息)
        - 成功时返回 (True, 章节数, None)
        - 失败时返回 (False, None, 错误信息)
    """
    try:
        import jmcomic
    except Exception:
        return False, None, "jmcomic 依赖不可用，请确认插件依赖已安装"

    try:
        output_dir = os.path.abspath(output_dir)
        os.makedirs(output_dir, exist_ok=True)

        option_file = _write_unique_option_file(output_dir, proxy=proxy, option_dir=option_dir)

        try:
            option = jmcomic.create_option_by_file(option_file)

            def get_album_info():
                client = option.new_jm_client()
                album = client.get_album_detail(album_id)
                return len(album)

            chapter_count = await asyncio.to_thread(get_album_info)
            return True, chapter_count, None
        finally:
            try:
                os.remove(option_file)
            except Exception:
                pass
    except Exception:
        logging.getLogger(__name__).exception("获取 JM 章节信息失败")
        return False, None, "获取章节信息失败，请检查 JM ID、网络和代理配置"


async def async_download_album(
    album_id: str,
    output_dir: str,
    option_dir: str,
    proxy: str = "",
    only_first_chapter: bool = False,
    chapter_index: Optional[int] = None,
    chapter_range: Optional[Tuple[int, int]] = None,
) -> Tuple[bool, Optional[str], Optional[int]]:
    """异步下载 JMComic 本子。
    
    支持四种下载模式：
    1. 下载整本（only_first_chapter=False 且未指定 chapter_index 和 chapter_range）
    2. 仅下载第一章（only_first_chapter=True）
    3. 下载指定章节（指定 chapter_index，1-based）
    4. 下载章节范围（指定 chapter_range，如 (1, 5) 表示下载第1到5章）
    
    Args:
        album_id: 本子 ID
        output_dir: 下载根目录
        option_dir: 临时 option 文件目录
        proxy: JMComic HTTP 代理
        only_first_chapter: 是否仅下载第一章
        chapter_index: 指定章节号（从 1 开始），优先级高于 only_first_chapter
        chapter_range: 指定章节范围（起始章节, 结束章节），优先级最高
    
    Returns:
        (是否成功, 图片目录或错误信息, 总章节数或 None)
    """
    try:
        import jmcomic
    except Exception:
        return False, "jmcomic 依赖不可用，请确认插件依赖已安装", None

    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)
    task_download_dir = Path(option_dir) / f"jm_download_{uuid.uuid4().hex}"
    task_download_dir.mkdir(parents=True, exist_ok=False)

    option_file = _write_unique_option_file(
        str(task_download_dir), proxy=proxy, option_dir=option_dir
    )

    try:
        try:
            option = jmcomic.create_option_by_file(option_file)
        except Exception:
            logging.getLogger(__name__).exception("创建 jmcomic 配置失败")
            return False, "JM 配置初始化失败，请检查下载目录和代理配置", None

        # 解析并确定要下载的章节
        photo_id_to_download = None
        photo_ids_to_download = None
        total_chapters = None
        download_chapter_index = None

        if chapter_range is not None or chapter_index is not None or only_first_chapter:
            try:
                def get_album_chapters():
                    client = option.new_jm_client()
                    album = client.get_album_detail(album_id)
                    total = len(album)
                    return list(album), total

                chapters_list, total_chapters = await asyncio.to_thread(get_album_chapters)

                if total_chapters == 0:
                    return False, "本子无章节信息", None

                if chapter_range is not None:
                    start_chapter, end_chapter = chapter_range
                    photo_ids_to_download = []
                    for i in range(start_chapter - 1, min(end_chapter, total_chapters)):
                        photo_id = chapters_list[i].photo_id
                        if photo_id is not None:
                            photo_ids_to_download.append(photo_id)
                    if not photo_ids_to_download:
                        return False, "指定章节没有可下载的图片信息", None
                elif chapter_index is not None:
                    idx = chapter_index - 1
                    if idx < 0 or idx >= total_chapters:
                        return False, "指定章节超出范围", None
                    download_chapter_index = idx

                    if download_chapter_index is not None:
                        photo_id_to_download = chapters_list[download_chapter_index].photo_id
                        if photo_id_to_download is None:
                            return False, "无法获取指定章节信息", None
                else:
                    download_chapter_index = 0
                    photo_id_to_download = chapters_list[download_chapter_index].photo_id
                    if photo_id_to_download is None:
                        return False, "无法获取指定章节信息", None
            except Exception:
                logging.getLogger(__name__).exception("获取 JM 章节列表失败")
                return False, "获取章节信息失败，请检查 JM ID 和网络配置", None

        try:
            if photo_ids_to_download is not None:
                for photo_id in photo_ids_to_download:
                    await asyncio.to_thread(jmcomic.download_photo, photo_id, option)
            elif download_chapter_index is not None:
                await asyncio.to_thread(jmcomic.download_photo, photo_id_to_download, option)
            else:
                await asyncio.to_thread(jmcomic.download_album, album_id, option)
        except Exception:
            logging.getLogger(__name__).exception("JM 图片下载失败")
            return False, "下载失败，请检查 JM 网络、代理和磁盘空间", None

        # 获取本子标题，用于临时整理目录和用户提示；接口异常时回退到 ID。
        album_title = str(album_id)
        try:
            def get_album_title() -> Any:
                detail = option.new_jm_client().get_album_detail(album_id)
                return getattr(detail, "name", None) or getattr(detail, "title", None)

            fetched_title = await asyncio.to_thread(get_album_title)
            if fetched_title:
                album_title = str(fetched_title).strip() or album_title
        except Exception:
            pass
        safe_album_title = sanitize_filename(album_title) or sanitize_filename(str(album_id)) or "jm_download"

        # 任务目录是本次 jmcomic 下载的唯一作用域，不读取共享下载缓存。
        task_images = sorted(
            [
                p.resolve()
                for p in task_download_dir.rglob("*")
                if p.is_file()
                and p.suffix.lower() in {".jpg", ".jpeg", ".png", ".webp"}
            ],
            key=_natural_path_key,
        )
        if not task_images:
            return False, "未找到本次下载新增的图片", None

        # 将图片扁平复制到短文件名目录。jmcomic 的目录名通常就是完整标题；若继续
        # 保留该相对路径，会在 Windows 上形成“标题/标题/图片”的重复长路径并触发
        # WinError 3（传统 MAX_PATH 限制）。排序已经在 task_images 中确定，因此编号
        # 文件仍能保持章节和页序。
        aggregate_title = safe_album_title[:80].rstrip(" ._") or "jm_download"
        aggregate_dir = Path(option_dir) / f"{aggregate_title}_{uuid.uuid4().hex[:8]}"
        try:
            aggregate_dir.mkdir(parents=True, exist_ok=False)
            for index, image_path in enumerate(task_images, 1):
                suffix = image_path.suffix.lower()
                destination = aggregate_dir / f"{index:06d}{suffix}"
                shutil.copy2(image_path, destination)
        except Exception:
            logging.getLogger(__name__).exception("整理 JM 下载图片失败")
            shutil.rmtree(aggregate_dir, ignore_errors=True)
            return False, "整理下载图片失败，请检查磁盘空间和文件权限", None

        return True, str(aggregate_dir), total_chapters
    finally:
        try:
            os.remove(option_file)
        except Exception:
            pass
        shutil.rmtree(task_download_dir, ignore_errors=True)



# =============================================================================
# 命令处理
# =============================================================================

def _metadata_value(value: Any, key: str) -> Any:
    if isinstance(value, dict):
        return value.get(key)
    return getattr(value, key, None)


def _message_info_value(message: Any, key: str) -> Any:
    return _metadata_value(getattr(message, "message_info", None), key)


def _normalized_permission_list(command: Any, key: str) -> set[str]:
    raw_list = command.get_config(key, []) or []
    return {str(item).strip() for item in raw_list if str(item).strip()}


def _check_permission(command: Any) -> Tuple[bool, Optional[str]]:
    """按群聊和用户两层名单判断当前命令是否允许执行。"""
    message_info = getattr(command.message, "message_info", None)
    group_info = _metadata_value(message_info, "group_info")
    user_info = _metadata_value(message_info, "user_info")
    raw_group_id = _metadata_value(group_info, "group_id")
    raw_user_id = _metadata_value(user_info, "user_id")
    group_id = str(raw_group_id).strip() if raw_group_id is not None else ""
    user_id = str(raw_user_id).strip() if raw_user_id is not None else ""

    group_mode = str(command.get_config("permission.mode", "off") or "off").strip().lower()
    group_list = _normalized_permission_list(command, "permission.group_list")
    if group_id and group_mode == "whitelist" and group_id not in group_list:
        return False, "本群未开启该功能"
    if group_id and group_mode == "blacklist" and group_id in group_list:
        return False, "本群已禁用该功能"

    user_mode = str(command.get_config("permission.user_mode", "off") or "off").strip().lower()
    user_list = _normalized_permission_list(command, "permission.user_list")
    if user_mode == "whitelist" and (not user_id or user_id not in user_list):
        return False, "你不在本插件的用户白名单中"
    if user_mode == "blacklist" and user_id and user_id in user_list:
        return False, "你已被禁止使用本插件"

    return True, None


# 兼容已有测试和第三方调用；新代码统一使用 _check_permission。
def _check_group_permission(command: Any) -> Tuple[bool, Optional[str]]:
    return _check_permission(command)


class SDKCommandBridge:
    """在迁移期间让既有命令逻辑使用原生 SDK 发送能力。"""

    ctx: Any

    async def send_text(self, content: str, **kwargs: Any) -> bool:
        del kwargs
        return bool(await self.ctx.send.text(content, self._stream_id))


class JMSotuCommand(SDKCommandBridge, BaseCommand):
    """JM 以图搜本命令处理器"""
    command_name = "jm搜图"
    command_description = "发送图片进行搜图，并自动在 JM 中搜索结果。用法：发送图片后输入 /jm搜图"
    command_pattern = (
        r"^(?:"
        r"\[回复 [^\r\n\]]*?\]，说：\s*"
        r"|\[回复<[^>\r\n]*>：[^\r\n\]]*?\]，说：\s*"
        r"|\[回复了[^\r\n\]]*?:[^\r\n\]]*\]\s*"
        r"|\[回复了一条消息，但原消息已无法访问\]\s*"
        r")?"
        r"/jm搜图\s*$"
    )
    intercept_message = True

    async def execute(self) -> Tuple[bool, Optional[str], bool]:
        # 群名单检查（私聊放行）
        allowed, reason = _check_group_permission(self)
        if not allowed:
            await self.send_text(reason)
            return True, None, True

        if not aiohttp:
            await self.send_text("依赖缺失: aiohttp")
            return True, None, True

        # 1. 获取当前消息或被引用消息中的图片。明确命令不使用近期消息兜底，避免群聊串图。
        try:
            image_data = await _resolve_command_image(
                self.host_message,
                self.ctx,
                stream_id=self._stream_id,
                session=self.http_session,
                max_bytes=self.sotu_config.max_upload_bytes,
            )
        except (ValueError, RuntimeError):
            self.ctx.logger.exception("读取搜图命令图片失败")
            await self.send_text("图片读取失败，请确认图片仍可访问且未超过大小限制后重试")
            return True, None, True
        except Exception:
            self.ctx.logger.exception("解析搜图命令图片失败")
            await self.send_text("图片解析失败，请重新发送图片或重新引用后重试")
            return True, None, True

        if not image_data:
            await self.send_text("未检测到图片，请在消息中附带图片，或引用一条含图片的消息后输入 /jm搜图")
            return True, None, True

        await self.send_text("正在进行以图搜图...")

        try:
            results = await search_image(image_data, self.sotu_config, self.http_session)
        except ImageAcquisitionError:
            self.ctx.logger.exception("规范化搜图图片失败")
            await self.send_text("图片读取失败，请确认图片格式有效且未超过大小限制后重试")
            return True, None, True
        except ImageProviderTimeoutError:
            self.ctx.logger.exception("以图搜本 provider 请求超时")
            await self.send_text(
                f"搜图服务响应超时（已自动重试 1 次，每次最多等待 {self.sotu_config.timeout_seconds} 秒），请稍后重试"
            )
            return True, None, True
        except ImageProviderError:
            self.ctx.logger.exception("以图搜本 provider 调用失败")
            await self.send_text("搜图服务调用失败，请稍后重试；若持续失败请检查插件日志和搜图配置")
            return True, None, True

        if not results:
            await self.send_text("搜图完成，但没有符合相似度要求的结果")
            return True, None, True

        # 4. 展示前三条图片识别候选，随后按相似度顺序逐条在 JM 中甄别。
        image_candidates = results[:3]
        candidate_message = "搜图候选（将依次净化并在 JM 中甄别）:\n"
        for index, result in enumerate(image_candidates, 1):
            candidate_message += (
                f"{index}. [{result.similarity:g}%] {result.title}\n"
            )
        await self.send_text(candidate_message.rstrip())

        # 5. 在 JM 中搜索
        jm_data_dir = self.get_config("jm.jm_data_dir", "")
        if not jm_data_dir:
            jm_data_dir = str(self.data_dir / "downloads")
        os.makedirs(jm_data_dir, exist_ok=True)
        option_dir = str(Path(self.runtime_dir) / "soutu")

        # 初始化 jmcomic option
        option = None
        option_file = None
        try:
            import jmcomic

            # 读取配置中的代理
            proxy = self.get_config("jm.proxy", "")
            if not proxy:
                # 尝试读取 sotu 的代理作为回退
                proxy = self.get_config("sotu.proxy", "")

            option_file = _write_unique_option_file(jm_data_dir, proxy=proxy, option_dir=option_dir)
            option = jmcomic.create_option_by_file(option_file)

        except Exception as e:
            self.ctx.logger.exception("JM 配置初始化失败")
            if option_file:
                try:
                    os.remove(option_file)
                except Exception:
                    pass
            await self.send_text("JM 配置初始化失败，请检查下载目录和代理配置后重试")
            return True, None, True

        if not option:
            try:
                if option_file:
                    os.remove(option_file)
            except Exception:
                pass
            await self.send_text("JM 配置初始化失败: option 未定义")
            return True, None, True

        try:
            for index, image_result in enumerate(image_candidates, 1):
                keywords = _soutu_jm_keyword_candidates(image_result.title)
                self.ctx.logger.info(
                    "JM 搜图候选 %d 检索词: %s",
                    index,
                    " | ".join(keywords) or image_result.title,
                )
            match = await _find_accurate_jm_match(image_candidates, option)
        finally:
            if option_file:
                try:
                    os.remove(option_file)
                except Exception:
                    pass

        if match is None:
            await self.send_text(
                "前三条搜图候选均未在 JM 中找到标题相似度足够高的准确结果；已过滤宽泛或疑似误匹配结果"
            )
            return True, None, True

        matched_image = match.image_result
        ranked_results = match.ranked_results
        best_score = ranked_results[0][0]
        await self.send_text(
            f"已命中准确结果: [{matched_image.similarity:g}%] {matched_image.title}\n"
            f"净化检索词: {match.keyword}\n"
            f"JM 标题匹配度: {best_score * 100:.1f}%"
        )

        # 6. 仅显示标题甄别通过的结果，并按匹配度排序。
        msg = f"JM 准确结果 ({len(ranked_results)}个):\n"
        for index, (score, album) in enumerate(ranked_results[:5], 1):
            msg += (
                f"{index}. ID: {album['id']} | {album['title']} | "
                f"{album.get('author', '未知')} | 匹配 {score * 100:.1f}%\n"
            )

        msg += "\n请输入 /jm ID 进行下载"
        if len(ranked_results) > 5:
            msg += f"\n(仅显示前5个，共甄别出 {len(ranked_results)} 个)"

        await self.send_text(msg)
        return True, None, True


class JMCommand(SDKCommandBridge, BaseCommand):
    """JM 本子下载命令处理器。

    命令格式：
    - /jm <ID>        下载指定 ID 的本子（多章节必须指定章节）
    - /jm <ID> <章节> 下载指定 ID 本子的指定章节

    执行流程：解析参数 → 检查章节 → 决策下载 → 合成 PDF → 上传 → 清理。
    """

    command_name = "jm"
    command_description = "下载或搜索 JM 本子。用法：/jm ID（多章节必须指定章节）或 /jm ID 章节号 或 /jm ID 起始-结束 或 /jm 关键词"
    command_pattern = r"^/jm(?:\s+(?P<args>.+))?$"

    async def execute(self) -> Tuple[bool, Optional[str], bool]:
        allowed, reason = _check_group_permission(self)
        if not allowed:
            await self.send_text(reason)
            return True, None, True
        return await self._execute()

    async def _execute(self) -> Tuple[bool, Optional[str], bool]:
        """执行命令主逻辑。
        
        功能：
        1. /jm 关键词 -> 搜索本子并返回列表
        2. /jm ID -> 下载指定本子
        3. /jm ID 章节数 -> 下载指定章节
        
        Returns:
            元组 (是否继续执行, 执行结果消息, 是否成功)
        """
        args_str = ""
        if self.matched_groups and "args" in self.matched_groups:
            args_str = self.matched_groups["args"] or ""
        args_str = args_str.strip()
        
        if not args_str:
            await self.send_text("用法：/jm ID 或 /jm ID 章节数")
            return True, None, True
        
        parts = args_str.split()
        album_id_or_keyword = parts[0]
        chapter_num = None
        search_page = 1
        
        # 判断是 ID 还是 关键词
        is_id = album_id_or_keyword.isdigit()
        
        if not is_id:
            # 如果是关键词，进行搜索
            
            # 尝试解析页码: /jm keyword page_num
            if len(parts) > 1 and parts[-1].isdigit():
                try:
                    search_page = int(parts[-1])
                    if search_page < 1:
                        search_page = 1
                    # 如果关键词包含空格，除了最后一个数字外都是关键词
                    album_id_or_keyword = " ".join(parts[:-1])
                except:
                    pass
            elif len(parts) > 1:
                 # 关键词本身包含空格
                 album_id_or_keyword = args_str

            await self.send_text(f"正在搜索: {album_id_or_keyword} (第{search_page}页)")
            
            jm_data_dir = str(self.data_dir / "downloads")
            os.makedirs(jm_data_dir, exist_ok=True)
            
            try:
                import jmcomic

                # 读取配置中的代理
                proxy = self.get_config("jm.proxy", "")
                if not proxy:
                    proxy = self.get_config("sotu.proxy", "")

                option_dir = str(Path(self.runtime_dir) / "jm_search")
                os.makedirs(option_dir, exist_ok=True)
                option_file = _write_unique_option_file(jm_data_dir, proxy=proxy, option_dir=option_dir)
                try:
                    option = jmcomic.create_option_by_file(option_file)
                    jm_results = await search_jm_by_keyword(album_id_or_keyword, option, page=search_page)
                finally:
                    try:
                        os.remove(option_file)
                    except Exception:
                        pass

                if not jm_results:
                    await self.send_text("未找到相关本子")
                    return True, None, True

                display_count = 10
                msg = f"搜索结果 (第{search_page}页, 显示{min(len(jm_results), display_count)}个):\n"
                for i, album in enumerate(jm_results[:display_count], 1):
                    msg += f"{i}. ID: {album['id']} | {album['title']}\n"

                msg += "\n请输入 /jm ID 进行下载"
                msg += f"\n请输入 /jm {album_id_or_keyword} {search_page + 1} 查看下一页"

                await self.send_text(msg)
                return True, None, True

            except Exception as e:
                self.ctx.logger.exception("JM 关键词搜索失败")
                await self.send_text("搜索失败，请检查 JM 网络或代理配置后重试")
                return True, None, True
                
        # 如果是 ID，继续原有的下载逻辑
        album_id = album_id_or_keyword
        
        chapter_num = None
        chapter_range = None
        
        if len(parts) > 1:
            chapter_param = parts[1]
            
            # 检查是否是章节范围（如 1-5 或 1-）
            if '-' in chapter_param:
                try:
                    range_parts = chapter_param.split('-')
                    if len(range_parts) == 2:
                        start_chapter = int(range_parts[0]) if range_parts[0] else None
                        end_chapter = int(range_parts[1]) if range_parts[1] else None
                        
                        if start_chapter is not None and start_chapter <= 0:
                            await self.send_text("起始章节必须为正整数")
                            return True, None, True
                        
                        if end_chapter is not None and end_chapter <= 0:
                            await self.send_text("结束章节必须为正整数")
                            return True, None, True
                        
                        if start_chapter is not None and end_chapter is not None and start_chapter > end_chapter:
                            await self.send_text("起始章节不能大于结束章节")
                            return True, None, True
                        
                        chapter_range = (start_chapter, end_chapter)
                except ValueError:
                    await self.send_text("章节格式错误，请使用：/jm ID 或 /jm ID 章节号 或 /jm ID 起始-结束")
                    return True, None, True
            else:
                # 单个章节号
                try:
                    chapter_num = int(chapter_param)
                    if chapter_num <= 0:
                        await self.send_text("章节数必须为正整数")
                        return True, None, True
                except ValueError:
                    await self.send_text("章节数必须为正整数")
                    return True, None, True

        # 用户和群聊权限已在命令入口统一检查。
        await self.send_text("开始下载")

        jm_data_dir = self.get_config("jm.jm_data_dir", "")
        if not jm_data_dir:
            jm_data_dir = str(self.data_dir / "downloads")
        option_dir = str(Path(self.runtime_dir) / "jm")
        os.makedirs(option_dir, exist_ok=True)
        napcat_base_url = self.get_config("jm.napcat_base_url")
        max_pdf_pages = self.get_config("jm.max_pdf_pages")

        success, chapter_count, error_msg = await check_album_chapters(
            album_id,
            output_dir=jm_data_dir,
            option_dir=option_dir,
            proxy=self.get_config("jm.proxy", ""),
        )

        if not success:
            self.ctx.logger.error("检查 JM 章节信息失败: %s", error_msg)
            await self.send_text("检查章节信息失败，请确认 JM ID、下载目录和网络配置后重试")
            return True, None, True

    # 决定下载策略
        only_first_chapter = False
        use_chapter_index = None
        use_chapter_range = None
        
        if chapter_count > 1:
            if chapter_range is not None:
                # 处理章节范围
                start_chapter, end_chapter = chapter_range
                
                # 如果没有指定起始章节，默认从第1章开始
                if start_chapter is None:
                    start_chapter = 1
                
                # 如果没有指定结束章节，默认下载到最后一章
                if end_chapter is None:
                    end_chapter = chapter_count
                
                # 调整范围不超过实际章节数
                if start_chapter > chapter_count:
                    start_chapter = chapter_count
                    await self.send_text(f"本子仅有{chapter_count}章，调整起始章节为第{start_chapter}章")
                
                if end_chapter > chapter_count:
                    end_chapter = chapter_count
                    await self.send_text(f"本子仅有{chapter_count}章，调整结束章节为第{end_chapter}章")
                
                use_chapter_range = (start_chapter, end_chapter)
                if start_chapter == end_chapter:
                    await self.send_text(f"检测到多章节本子({chapter_count}话)，下载第{start_chapter}章")
                else:
                    await self.send_text(f"检测到多章节本子({chapter_count}话)，下载第{start_chapter}到{end_chapter}章")
            elif chapter_num is not None:
                if chapter_num > chapter_count:
                    await self.send_text(f"本子仅有{chapter_count}章，章节号超出范围")
                    return True, None, True
                use_chapter_index = chapter_num
                await self.send_text(f"检测到多章节本子({chapter_count}话)，下载第{chapter_num}章")
            else:
                # 多章节本子但没有指定章节，提示用户
                await self.send_text(f"检测到多章节本子({chapter_count}话)，请指定要下载的章节")
                await self.send_text(f"例如：/jm {album_id} 1 或 /jm {album_id} 1-5")
                return True, None, True
        else:
            if chapter_num is not None:
                await self.send_text("单章节本子，忽略章节数参数")
            elif chapter_range is not None:
                await self.send_text("单章节本子，忽略章节范围参数")

        success, album_dir, total_chapters = await async_download_album(
            album_id,
            output_dir=jm_data_dir,
            option_dir=option_dir,
            proxy=self.get_config("jm.proxy", ""),
            only_first_chapter=only_first_chapter,
            chapter_index=use_chapter_index,
            chapter_range=use_chapter_range,
        )

        if not success:
            await self.send_text("下载失败")
            return True, album_dir, True

        album_name = os.path.basename(album_dir)
        await self.send_text(album_name)
        await self.send_text("下载成功")

    # 收集图片文件
        supported_extensions = {".jpg", ".jpeg", ".png", ".webp"}
        img_paths = sorted(
            [p for p in Path(album_dir).rglob("*") if p.suffix.lower() in supported_extensions],
            key=_natural_path_key,
        )

        if not img_paths:
            await self.send_text("未找到图片")
            self._cleanup_album_dir(album_dir)
            return True, None, True

        if len(img_paths) > max_pdf_pages:
            await self.send_text(f"页数超过 {max_pdf_pages}，不生成 PDF")
            self._cleanup_album_dir(album_dir)
            return True, None, True

    # 检查是否使用加密压缩包
        use_encrypted_zip = self.get_config("jm.use_encrypted_zip", False)
        fake_extension = sanitize_fake_extension(
            self.get_config("jm.fake_extension", ".dat")
        )

        album_title = re.sub(r"_[0-9a-f]{8}$", "", Path(album_dir).name)
        if use_encrypted_zip:
            return await self._send_encrypted_zip(img_paths, album_id, use_chapter_index, use_chapter_range, only_first_chapter, napcat_base_url, fake_extension, album_dir, album_title)
        else:
            return await self._send_pdf(img_paths, album_id, use_chapter_index, use_chapter_range, only_first_chapter, napcat_base_url, album_dir, album_title)

    @staticmethod
    def _cleanup_album_dir(album_dir: Optional[str]) -> None:
        """删除本次下载的图片目录。失败静默，避免影响主流程。"""
        if not album_dir:
            return
        try:
            if os.path.isdir(album_dir):
                shutil.rmtree(album_dir, ignore_errors=True)
        except Exception:
            pass

    @staticmethod
    def _safe_remove(*paths: str) -> None:
        for p in paths:
            if not p:
                continue
            try:
                if os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass

    async def _send_encrypted_zip(self, img_paths, album_id, use_chapter_index, use_chapter_range, only_first_chapter, napcat_base_url, fake_extension, album_dir=None, album_title=None):
        """生成并发送 AES ZIP。"""
        safe_name = build_artifact_name(
            album_id,
            use_chapter_index,
            use_chapter_range,
            only_first_chapter,
        )

        unique_token = uuid.uuid4().hex[:8]
        file_stem = f"{safe_name}_{unique_token}"
        task_dir = Path(self.runtime_dir) / "artifacts" / uuid.uuid4().hex
        task_dir.mkdir(parents=True, exist_ok=True)
        pdf_path = str(task_dir / f"{file_stem}.pdf")
        zip_path = str(task_dir / f"{file_stem}.zip")
        fake_zip_path = str(task_dir / f"{file_stem}{fake_extension}")

        try:
            try:
                await asyncio.to_thread(images_to_pdf_sync, img_paths, pdf_path)

                await asyncio.to_thread(pdf_to_encrypted_zip, pdf_path, zip_path, safe_name)

                await self.send_text("压缩并加密成功")

                shutil.move(zip_path, fake_zip_path)

                is_group = False
                group_id = None
                user_id = None

                try:
                    message_info = self.message.message_info
                    if message_info.group_info and message_info.group_info.group_id:
                        is_group = True
                        group_id = int(message_info.group_info.group_id)
                    elif message_info.user_info and message_info.user_info.user_id:
                        user_id = int(message_info.user_info.user_id)
                except Exception:
                    pass

                # 上传时用原始 safe_name 作为对外文件名（不暴露 unique_token）
                upload_name = f"{safe_name}{fake_extension}"
                if is_group:
                    ok, msg = await upload_pdf_via_napcat(
                        fake_zip_path, upload_name, "group", group_id, napcat_base_url,
                        session=self.http_session, content_type="application/zip"
                    )
                elif user_id:
                    ok, msg = await upload_pdf_via_napcat(
                        fake_zip_path, upload_name, "private", user_id, napcat_base_url,
                        session=self.http_session, content_type="application/zip"
                    )
                else:
                    await self.send_text("无法识别发送对象")
                    return True, None, True

                if not ok:
                    await self.send_text(f"上传失败：{msg or 'NapCat 未接受文件'}")
                    return True, msg, True

                await self.send_text(f"完成！密码是文件名（不含扩展名）：{safe_name}")
                return True, "完成", True

            except Exception as e:
                self.ctx.logger.exception("PDF/ZIP 处理失败")
                await self.send_text("处理失败，请检查磁盘空间、PDF 页数限制和插件日志后重试")
                return True, None, True
        finally:
            self._safe_remove(pdf_path, zip_path, fake_zip_path)
            shutil.rmtree(task_dir, ignore_errors=True)
            self._cleanup_album_dir(album_dir)

    async def _send_pdf(self, img_paths, album_id, use_chapter_index, use_chapter_range, only_first_chapter, napcat_base_url, album_dir=None, album_title=None):
        """生成并发送 PDF。"""
        safe_name = build_artifact_name(
            album_id,
            use_chapter_index,
            use_chapter_range,
            only_first_chapter,
        )

        unique_token = uuid.uuid4().hex[:8]
        file_stem = f"{safe_name}_{unique_token}"
        task_dir = Path(self.runtime_dir) / "artifacts" / uuid.uuid4().hex
        task_dir.mkdir(parents=True, exist_ok=True)
        pdf_path = str(task_dir / f"{file_stem}.pdf")

        try:
            try:
                await asyncio.to_thread(images_to_pdf_sync, img_paths, pdf_path)
            except Exception:
                self.ctx.logger.exception("PDF 生成失败")
                await self.send_text("PDF 生成失败，请检查图片内容、页数限制和磁盘空间")
                return True, None, True

            is_group = False
            group_id = None
            user_id = None

            try:
                message_info = self.message.message_info
                if message_info.group_info and message_info.group_info.group_id:
                    is_group = True
                    group_id = int(message_info.group_info.group_id)
                elif message_info.user_info and message_info.user_info.user_id:
                    user_id = int(message_info.user_info.user_id)
            except Exception:
                pass

            upload_name = f"{safe_name}.pdf"
            if is_group:
                ok, msg = await upload_pdf_via_napcat(
                    pdf_path, upload_name, "group", group_id, napcat_base_url, session=self.http_session
                )
            elif user_id:
                ok, msg = await upload_pdf_via_napcat(
                    pdf_path, upload_name, "private", user_id, napcat_base_url, session=self.http_session
                )
            else:
                await self.send_text("无法识别发送对象")
                return True, None, True

            if not ok:
                await self.send_text(f"上传失败：{msg}")
                return True, msg, True

            return True, "完成", True
        finally:
            self._safe_remove(pdf_path)
            shutil.rmtree(task_dir, ignore_errors=True)
            self._cleanup_album_dir(album_dir)



# =============================================================================
# 插件注册
# =============================================================================

class PluginSectionConfig(PluginConfigBase):
    __ui_label__ = "插件设置"
    __ui_icon__ = "package"
    __ui_order__ = 0

    enabled: bool = Field(
        default=True,
        description="控制 JM 插件是否启用。",
        json_schema_extra={"label": "启用插件", "hint": "关闭后插件不会响应 /jm 和 /jm搜图。"},
    )
    config_version: str = Field(
        default="2.0.0",
        description="插件配置结构版本，由插件自动维护。",
        json_schema_extra={"label": "配置版本", "hint": "请勿手动修改。", "disabled": True},
    )


class JmConfig(PluginConfigBase):
    __ui_label__ = "下载与文件"
    __ui_icon__ = "download"
    __ui_order__ = 1

    jm_data_dir: str = Field(
        default="",
        description="JM 图片的持久保存目录；留空时使用 MaiBot 分配的插件数据目录。",
        json_schema_extra={"label": "下载目录", "hint": "新手建议留空。填写时请使用 MaiBot 进程可读写的绝对路径。"},
    )
    proxy: str = Field(
        default="",
        description="访问 JMComic 时使用的 HTTP/HTTPS 代理。",
        json_schema_extra={"label": "JM 网络代理", "hint": "不需要代理请留空，例如 http://127.0.0.1:7890。"},
    )
    napcat_base_url: str = Field(
        default="http://127.0.0.1:3000",
        description="用于上传 PDF 或 ZIP 的 NapCat HTTP API 基础地址。",
        json_schema_extra={"label": "NapCat 地址", "hint": "通常保持 http://127.0.0.1:3000；端口需与 NapCat 配置一致。"},
    )
    max_pdf_pages: int = Field(
        default=500,
        ge=1,
        le=2000,
        description="单个 PDF 允许包含的最大图片页数。",
        json_schema_extra={"label": "PDF 最大页数", "hint": "默认 500。设置过大可能增加内存占用和处理时间。", "x-widget": "slider", "min": 1, "max": 2000, "step": 1},
    )
    use_encrypted_zip: bool = Field(
        default=False,
        description="下载完成后是否生成 AES 加密 ZIP，而不是直接上传 PDF。",
        json_schema_extra={"label": "生成加密 ZIP", "hint": "密码为输出文件名中的 JM 车牌号部分；不需要时请关闭。"},
    )
    fake_extension: str = Field(
        default=".dat",
        description="加密 ZIP 上传时显示的扩展名，不改变文件内部格式。",
        json_schema_extra={"label": "ZIP 伪装扩展名", "hint": "默认 .dat；接收后可改回 .zip 再解压。只允许填写简单扩展名。"},
    )


class SotuConfig(PluginConfigBase):
    __ui_label__ = "以图搜本"
    __ui_icon__ = "search"
    __ui_order__ = 2

    provider: Literal["soutubot", "saucenao"] = Field(
        default="soutubot",
        description="用于识别图片来源的搜图服务。",
        json_schema_extra={"label": "搜图服务", "hint": "推荐 SoutuBot，通常无需密钥；SauceNAO 仅作为兼容选项。"},
    )
    api_base: str = Field(
        default="https://soutubot.moe",
        description="SoutuBot 服务基础地址。",
        json_schema_extra={"label": "SoutuBot 地址", "hint": "通常无需修改。仅在使用可信镜像服务时填写其他 HTTPS 地址。"},
    )
    user_agent: str = Field(
        default="Mozilla/5.0",
        description="搜图请求使用的浏览器 User-Agent。",
        json_schema_extra={"label": "请求 User-Agent", "hint": "通常保持默认值，服务端明确要求时再修改。"},
    )
    factor: float = Field(
        default=1.2,
        ge=0.1,
        le=10.0,
        description="SoutuBot 的搜索系数。",
        json_schema_extra={"label": "SoutuBot 搜索系数", "hint": "推荐保持 1.2，错误数值可能导致服务端拒绝请求。"},
    )
    timeout_seconds: int = Field(
        default=30,
        ge=5,
        le=120,
        description="每次搜图网络请求的最长等待时间。",
        json_schema_extra={"label": "搜图超时（秒）", "hint": "超时后插件会进行一次有限重试。", "x-widget": "slider", "min": 5, "max": 120, "step": 1},
    )
    max_upload_bytes: int = Field(
        default=10 * 1024 * 1024,
        ge=1024,
        description="允许送往搜图服务的单张图片最大字节数。",
        json_schema_extra={"label": "图片大小上限（字节）", "hint": "默认 10485760，即 10 MiB。过大的图片会在上传前被拒绝。"},
    )
    max_results: int = Field(
        default=5,
        ge=1,
        le=20,
        description="搜图服务返回后最多保留的候选数量。",
        json_schema_extra={"label": "候选结果上限", "hint": "插件会展示前三个候选，并按顺序尝试匹配 JM。", "x-widget": "slider", "min": 1, "max": 20, "step": 1},
    )
    min_similarity: float = Field(
        default=40.0,
        ge=0,
        le=100,
        description="保留搜图结果及甄别 JM 标题时使用的最低相似度。",
        json_schema_extra={"label": "最低相似度", "hint": "默认 40。调高可减少误匹配，但也可能漏掉翻译标题。", "x-widget": "slider", "min": 0, "max": 100, "step": 1},
    )
    flaresolverr_url: str = Field(
        default="",
        description="可选的 FlareSolverr 服务地址，仅用于 SoutuBot 首页握手回退。",
        json_schema_extra={"label": "FlareSolverr 地址", "hint": "新手请留空。仅填写自己部署且可信的 HTTP/HTTPS 地址。"},
    )
    api_key: str = Field(
        default="",
        description="选择 SauceNAO 时使用的个人 API Key。",
        json_schema_extra={"label": "SauceNAO API Key", "hint": "仅 provider 选择 SauceNAO 时填写；不要截图、公开或提交到仓库。"},
    )
    proxy: str = Field(
        default="",
        description="访问搜图服务时使用的 HTTP/HTTPS 代理。",
        json_schema_extra={"label": "搜图网络代理", "hint": "不需要代理请留空，例如 http://127.0.0.1:7890。"},
    )


class PermissionConfig(PluginConfigBase):
    __ui_label__ = "使用权限"
    __ui_icon__ = "shield"
    __ui_order__ = 3

    mode: Literal["off", "whitelist", "blacklist"] = Field(
        default="off",
        description="群聊权限模式：不限制、白名单或黑名单。",
        json_schema_extra={"label": "群聊名单模式", "hint": "白名单只允许列表中的群，黑名单禁止列表中的群；私聊不受群名单影响。"},
    )
    group_list: List[str] = Field(
        default_factory=list,
        description="按群聊名单模式生效的群号列表。",
        json_schema_extra={"label": "群号列表", "hint": "填写群号，例如 [\"123456789\"]。模式为“不限制”时此列表不生效。"},
    )
    user_mode: Literal["off", "whitelist", "blacklist"] = Field(
        default="off",
        description="用户权限模式：不限制、白名单或黑名单。",
        json_schema_extra={"label": "用户名单模式", "hint": "白名单只允许列表中的 QQ，黑名单禁止列表中的 QQ；同时作用于群聊和私聊。"},
    )
    user_list: List[str] = Field(
        default_factory=list,
        description="按用户名单模式生效的 QQ 号列表。",
        json_schema_extra={"label": "用户 QQ 列表", "hint": "填写 QQ 号，例如 [\"123456789\"]。模式为白名单时仅允许列表中的用户，模式为黑名单时禁止列表中的用户。"},
    )


class JMPluginConfig(PluginConfigBase):
    plugin: PluginSectionConfig = Field(default_factory=PluginSectionConfig)
    jm: JmConfig = Field(default_factory=JmConfig)
    sotu: SotuConfig = Field(default_factory=SotuConfig)
    permission: PermissionConfig = Field(default_factory=PermissionConfig)


def _command_message(message: Any, group_id: str, user_id: str, stream_id: str) -> Any:
    """补齐旧命令逻辑仍需的最小消息视图。"""
    if message is not None and not isinstance(message, dict) and hasattr(message, "message_info"):
        return message

    source = message if isinstance(message, dict) else {}
    group_info = SimpleNamespace(group_id=group_id) if group_id else None
    user_info = SimpleNamespace(user_id=user_id) if user_id else None
    message_info = SimpleNamespace(group_info=group_info, user_info=user_info)
    return SimpleNamespace(
        message_info=message_info,
        message_segment=source.get("message_segment") or source.get("segments"),
        image_data=source.get("image_data"),
        content=source.get("content"),
        chat_stream=SimpleNamespace(stream_id=stream_id),
        session_id=stream_id,
    )


class JMPlugin(MaiBotPlugin):
    """JMComic 下载与以图搜本插件。"""

    config_model = JMPluginConfig

    def __init__(self) -> None:
        super().__init__()
        self._download_lock = asyncio.Lock()
        self._http_session: Optional[aiohttp.ClientSession] = None
        self._retired_http_sessions: List[aiohttp.ClientSession] = []

    async def on_load(self) -> None:
        self.ctx.paths.data_dir.mkdir(parents=True, exist_ok=True)
        self.ctx.paths.runtime_dir.mkdir(parents=True, exist_ok=True)
        self._http_session = aiohttp.ClientSession(
            timeout=aiohttp.ClientTimeout(total=self.config.sotu.timeout_seconds)
        )
        self.ctx.logger.info("JM 插件已通过 maibot_sdk 加载")

    async def on_unload(self) -> None:
        sessions = [self._http_session, *self._retired_http_sessions]
        self._http_session = None
        self._retired_http_sessions = []
        for session in sessions:
            if session is not None and not session.closed:
                await session.close()
        self.ctx.logger.info("JM 插件已卸载")

    async def on_config_update(self, scope: str, config_data: dict[str, object], version: str) -> None:
        del scope, config_data, version
        old_session = self._http_session
        self._http_session = aiohttp.ClientSession(
            timeout=aiohttp.ClientTimeout(total=self.config.sotu.timeout_seconds)
        )
        if old_session is not None and not old_session.closed:
            self._retired_http_sessions.append(old_session)
        self.ctx.logger.info("JM 插件配置已更新")

    def _bridge_command(self, command_type: type[BaseCommand], kwargs: Dict[str, Any]) -> BaseCommand:
        config_data = self.config.model_dump(mode="python")
        if not config_data["jm"]["jm_data_dir"]:
            config_data["jm"]["jm_data_dir"] = str(self.ctx.paths.data_dir / "downloads")

        stream_id = str(kwargs.get("stream_id") or "")
        command = command_type(
            message=_command_message(
                kwargs.get("message"),
                str(kwargs.get("group_id") or ""),
                str(kwargs.get("user_id") or ""),
                stream_id,
            ),
            plugin_config=config_data,
        )
        command.ctx = self.ctx
        command.host_message = kwargs.get("message")
        command.data_dir = self.ctx.paths.data_dir
        command.runtime_dir = self.ctx.paths.runtime_dir
        command.http_session = self._http_session
        command.sotu_config = self.config.sotu
        command._stream_id = stream_id
        matched_groups = kwargs.get("matched_groups")
        command.set_matched_groups(matched_groups if isinstance(matched_groups, dict) else {})
        return command

    @Command(
        "jm",
        description="下载或搜索 JM 本子",
        pattern=r"^/jm(?:\s+(?P<args>.+))?$",
        timeout_ms=600000,
    )
    async def handle_jm(self, **kwargs: Any):
        command = self._bridge_command(JMCommand, kwargs)
        allowed, reason = _check_group_permission(command)
        if not allowed:
            await command.send_text(reason)
            return True, None, True
        async with self._download_lock:
            return await command._execute()

    @Command(
        "jm搜图",
        description="使用当前消息或引用消息中的图片搜索 JM 本子",
        pattern=(
            r"^(?:"
            r"\[回复 [^\r\n\]]*?\]，说：\s*"
            r"|\[回复<[^>\r\n]*>：[^\r\n\]]*?\]，说：\s*"
            r"|\[回复了[^\r\n\]]*?:[^\r\n\]]*\]\s*"
            r"|\[回复了一条消息，但原消息已无法访问\]\s*"
            r")?"
            r"/jm搜图\s*$"
        ),
    )
    async def handle_soutu(self, **kwargs: Any):
        command = self._bridge_command(JMSotuCommand, kwargs)
        return await command.execute()


def create_plugin() -> JMPlugin:
    return JMPlugin()
