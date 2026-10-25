#!/usr/bin/env python3
"""Сборщик VLESS+Reality серверов с SNI под российские домены (для «белых списков»).

Откуда берёт (см. sources.txt):
  discover: — автопоиск свежих репозиториев на GitHub по ключевым словам
  repo:     — все текстовые файлы указанного репозитория
  search:   — поиск по коду GitHub (нужен токен, в Actions есть GITHUB_TOKEN)
  url:      — прямая ссылка на список / подписку
  tg:       — публичный Telegram-канал (веб-превью t.me/s/<канал>)

Что делает:
  1. достаёт vless://, оставляет Reality с SNI под российские домены (любой транспорт);
  2. DNS + TCP-проверка (отсев мёртвых, задержка);
  3. поднимает каждый сервер в Xray и через него узнаёт ВЫХОДНОЙ IP (куда реально выходит трафик)
     и скорость скачивания;
  4. сортировка по скорости, не больше 2 серверов на один адрес, всего до 450;
  5. имя по выходному IP на английском: «🇩🇪 Germany, Frankfurt».

Результат (папка out/):
  whitelist_ru_sni.txt        — основной список, самые быстрые сверху
  whitelist_ru_sni_b64.txt    — то же, base64-подпиской
  whitelist_ru_sni_ruip.txt   — только серверы, чей АДРЕС (вход) находится в РФ
  report.txt                  — сколько серверов отсеялось на каждом шаге и почему

Только стандартная библиотека Python 3.9+ (для проверки нужны xray и curl).
"""
import argparse
import base64
import concurrent.futures as cf
import html
import ipaddress
import itertools
import json
import os
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse as up
import urllib.request as ur
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).parent
OUT = ROOT / "out"
SOURCES_FILE = ROOT / "sources.txt"

# ───────────────────────────── НАСТРОЙКИ ─────────────────────────────
# Домены маскировки. Совпадение — точное или по поддомену (api.vk.com тоже подойдёт).
TIER1 = [  # то, что просили в первую очередь: VK, Яндекс, Max, Ozon
    "vk.com", "vk.ru", "vkvideo.ru", "userapi.com", "vkuser.net",
    "yandex.ru", "yandex.com", "yandex.net", "ya.ru", "yastatic.net", "yandexcloud.net",
    "max.ru", "oneme.ru",
    "ozon.ru", "ozone.ru",
]
TIER2 = [  # прочие российские сервисы не на .ru
    "ok.ru", "mail.ru", "mycdn.me", "dzen.ru", "kinopoisk.ru", "rutube.ru",
    "2gis.com", "tbank.ru", "tinkoff.ru", "sber.ru",
]
RU_TLDS = (".ru", ".su", ".xn--p1ai")  # любой сайт в российской зоне тоже считается подходящим SNI

ALLOWED_TYPES = None    # None = любые транспорты (tcp, grpc, xhttp, ws, h2, httpupgrade, kcp…); иначе например {"tcp", "grpc"}

MAX_TOTAL = 450         # итоговый размер списка
MAX_PER_IP = 2          # не больше стольких серверов на один адрес
MAX_TEST = 1500         # сколько кандидатов максимум гонять через Xray
SPEED_WORKERS = 24      # сколько Xray запускать параллельно
SPEED_URL = "https://speed.cloudflare.com/__down?bytes=25000000"
SPEED_TIMEOUT = 8       # секунд на измерение скорости (среднее за окно)
EXIT_TIMEOUT = 6        # секунд на запрос «какой у меня IP» через сервер
EXIT_URLS = ["https://www.cloudflare.com/cdn-cgi/trace", "https://api64.ipify.org"]
TG_PAGES = 5            # страниц истории у каждого канала (~20 постов на страницу)
TG_MAX_AGE_DAYS = 14    # старые посты пропускаем
GH_SEARCH_PAGES = 2     # страниц выдачи на каждый запрос поиска по коду (по 100 файлов)
DISCOVER_DAYS = 14      # автопоиск: берём репозитории, обновлявшиеся за последние N дней
MAX_DISCOVER = 60       # автопоиск: максимум репозиториев
FILES_PER_REPO = 60     # файлов из репозитория, указанного в repo:
FILES_PER_FOUND = 25    # файлов из репозитория, найденного автопоиском
GEO_LANG = "en"         # язык названий стран/городов
# ─────────────────────────────────────────────────────────────────────

UA = "Mozilla/5.0 (compatible; reality-collector/1.0)"
VLESS_RE = re.compile(r"vless://[^\s<>\"'`]+")
UUID_RE = re.compile(r"^[0-9a-fA-F]{8}-(?:[0-9a-fA-F]{4}-){3}[0-9a-fA-F]{12}$")
PBK_RE = re.compile(r"^[A-Za-z0-9_-]{43}$")
SID_RE = re.compile(r"^(?:[0-9a-fA-F]{2}){0,8}$")
TEXT_EXT = {"", ".txt", ".md", ".json", ".yaml", ".yml", ".conf", ".sub", ".list"}
GOOD_NAME = re.compile(r"reality|vless|white|sni|ru|sub|mix|all|config|vpn|v2ray|xray", re.I)
DEFAULT_SEARCH_DOMAINS = ("vk.com", "vk.ru", "yandex.ru", "ya.ru", "max.ru", "ozon.ru", "userapi.com")
DEFAULT_DISCOVER = ["vless reality", "vless reality russia whitelist", "v2ray configs",
                    "xray subscription", "vpn configs russia", "белые списки vless"]
_ports = itertools.count(20000)


def log(*a):
    print(*a, file=sys.stderr, flush=True)


# ───────────────────────────── сеть ─────────────────────────────
def http(url, headers=None, data=None, timeout=25, max_bytes=8_000_000, retries=2):
    h = {"User-Agent": UA}
    h.update(headers or {})
    for i in range(retries + 1):
        try:
            req = ur.Request(url, data=data, headers=h)
            with ur.urlopen(req, timeout=timeout) as r:
                return r.read(max_bytes).decode("utf-8", "ignore")
        except urllib.error.HTTPError as e:
            if e.code in (404, 410, 451):
                return None
            if e.code in (403, 429) and "api.github.com" in url:
                log(f"  ! GitHub API {e.code}, жду 30 с")
                time.sleep(30)
        except Exception:
            pass
        time.sleep(1.5 * (i + 1))
    return None


def gh_api(url, token):
    h = {"Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"}
    if token:
        h["Authorization"] = f"Bearer {token}"
    txt = http(url, headers=h)
    try:
        return json.loads(txt) if txt else None
    except ValueError:
        return None


# ───────────────────────── разбор ссылок ─────────────────────────
def match_tier(sni):
    """1 — VK/Яндекс/Max/Ozon, 2 — другие российские сервисы, 3 — любой домен в зоне .ru/.su/.рф, 0 — не российский."""
    s = sni.lower().rstrip(".")
    for tier, domains in ((1, TIER1), (2, TIER2)):
        for d in domains:
            if s == d or s.endswith("." + d):
                return tier
    return 3 if s.endswith(RU_TLDS) else 0


def try_b64(text):
    s = re.sub(r"\s+", "", text)
    if len(s) < 40 or not re.fullmatch(r"[A-Za-z0-9+/_=-]+", s):
        return ""
    s = s.replace("-", "+").replace("_", "/")
    s += "=" * (-len(s) % 4)
    try:
        return base64.b64decode(s).decode("utf-8", "ignore")
    except Exception:
        return ""


def extract_links(text, unescape_html=False):
    text = html.unescape(text) if unescape_html else text.replace("&amp;", "&")
    if "vless://" not in text:
        text = try_b64(text) or text
    return [m.rstrip(".,;)]}»") for m in VLESS_RE.findall(text)]


def public_host(host):
    if not host:
        return False
    try:
        ip = ipaddress.ip_address(host)
        return not (ip.is_private or ip.is_loopback or ip.is_link_local
                    or ip.is_multicast or ip.is_unspecified or ip.is_reserved)
    except ValueError:
        return "." in host and host != "localhost" and not host.endswith(".local")


def parse_vless(link, keep_other=False, why=None):
    """Возвращает dict или None. В why (Counter) записывается причина отказа."""
    def no(reason):
        if why is not None:
            why[reason] += 1
        return None

    try:
        u = up.urlsplit(link)
        port = u.port
        host = u.hostname
    except ValueError:
        return no("bad_url")
    if u.scheme != "vless" or not u.username or not port:
        return no("bad_url")
    if not public_host(host):
        return no("bad_host")
    if not UUID_RE.match(u.username):
        return no("bad_uuid")
    q = {k.lower(): v for k, v in up.parse_qsl(u.query, keep_blank_values=True)}
    if q.get("security", "").lower() != "reality":
        return no("not_reality")
    if q.get("encryption", "none").lower() not in ("none", ""):
        return no("vless_encryption")  # VLESS-шифрование (ML-KEM) клиенты почти не понимают
    typ = (q.get("type") or "tcp").lower()
    if ALLOWED_TYPES is not None and typ not in ALLOWED_TYPES:
        return no("transport_filtered")
    if not PBK_RE.match(q.get("pbk", "")) or not SID_RE.match(q.get("sid", "")):
        return no("bad_pbk_sid")
    sni = (q.get("sni") or q.get("servername") or "").strip().lower()
    if not sni:
        return no("no_sni")
    tier = match_tier(sni)
    if tier == 0 and not keep_other:
        return no("sni_not_russian")
    return {
        "base": link.split("#", 1)[0], "q": q, "type": typ,
        "host": host.lower(), "port": port, "uuid": u.username.lower(),
        "sni": sni, "tier": tier,
    }


# ───────────────────────────── источники ─────────────────────────────
def load_sources():
    src = {"discover": [], "repo": [], "search": [], "url": [], "tg": []}
    if SOURCES_FILE.exists():
        for line in SOURCES_FILE.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#") or ":" not in line:
                continue
            kind, val = line.split(":", 1)
            kind, val = kind.strip().lower(), val.strip()
            if kind in src and val:
                src[kind].append(val)
    if not src["search"]:
        src["search"] = [f'"security=reality" "sni={d}"' for d in DEFAULT_SEARCH_DOMAINS]
    if not src["discover"]:
        src["discover"] = list(DEFAULT_DISCOVER)
    return src


def to_raw(html_url):
    m = re.match(r"^https://github\.com/([^/]+/[^/]+)/blob/([^/]+)/(.+)$", html_url)
    return f"https://raw.githubusercontent.com/{m.group(1)}/{m.group(2)}/{m.group(3)}" if m else None


def gh_search_files(queries, token):
    """Поиск по коду. Лимит у GitHub — 10 запросов в минуту, поэтому пауза 7 с."""
    urls = []
    for q in queries:
        for page in range(1, GH_SEARCH_PAGES + 1):
            data = gh_api("https://api.github.com/search/code?per_page=100&page=%d&q=%s"
                          % (page, up.quote(q)), token)
            time.sleep(7)
            items = (data or {}).get("items") or []
            urls += [r for r in (to_raw(i.get("html_url", "")) for i in items) if r]
            if len(items) < 100:
                break
        log(f"  search {q[:60]} → всего файлов {len(set(urls))}")
    return list(dict.fromkeys(urls))


def discover_repos(queries, token, skip):
    """Ищет свежие репозитории по ключевым словам, чтобы не зависеть от заранее известного списка."""
    since = (datetime.now(timezone.utc) - timedelta(days=DISCOVER_DAYS)).strftime("%Y-%m-%d")
    found = []
    for q in queries:
        data = gh_api("https://api.github.com/search/repositories?per_page=50&sort=updated&order=desc&q="
                      + up.quote(f"{q} pushed:>={since}"), token)
        time.sleep(2.5)
        for it in (data or {}).get("items") or []:
            name = it.get("full_name")
            if name and not it.get("archived") and name.lower() not in skip and name not in found:
                found.append(name)
        log(f"  discover «{q}» → репозиториев {len(found)}")
        if len(found) >= MAX_DISCOVER:
            break
    return found[:MAX_DISCOVER]


def repo_file_urls(repo, token, limit):
    data = gh_api(f"https://api.github.com/repos/{repo}/git/trees/HEAD?recursive=1", token)
    files = []
    for t in (data or {}).get("tree", []):
        if t.get("type") != "blob" or t.get("size", 0) > 4_000_000:
            continue
        if os.path.splitext(t["path"])[1].lower() in TEXT_EXT:
            files.append(t["path"])
    files = sorted(files, key=lambda p: (not GOOD_NAME.search(p), p))[:limit]
    return [f"https://raw.githubusercontent.com/{repo}/HEAD/{up.quote(p)}" for p in files]


def fetch_tg(channel):
    channel = re.sub(r"^(https?://)?(t\.me/(s/)?)?@?", "", channel.strip()).strip("/")
    if not re.fullmatch(r"[A-Za-z0-9_]{4,64}", channel):
        log(f"  ! странное имя канала: {channel}")
        return []
    cutoff = datetime.now(timezone.utc) - timedelta(days=TG_MAX_AGE_DAYS)
    links, before = [], None
    for _ in range(TG_PAGES):
        page = http(f"https://t.me/s/{channel}" + (f"?before={before}" if before else ""))
        chunks = (page or "").split('data-post="')[1:]
        ids, oldest = [], None
        for ch in chunks:
            m = re.match(r"[\w]+/(\d+)", ch)
            if not m:
                continue
            ids.append(int(m.group(1)))
            tm = re.search(r'<time[^>]*datetime="([^"]+)"', ch)
            try:
                ts = datetime.fromisoformat(tm.group(1)) if tm else None
            except ValueError:
                ts = None
            if ts:
                oldest = ts if oldest is None else min(oldest, ts)
            if ts is None or ts >= cutoff:
                links += extract_links(ch, unescape_html=True)
        if not ids or (oldest and oldest < cutoff):
            break
        before = min(ids)
        time.sleep(1)
    return links


# ───────────────── проверка через Xray, выходной IP, гео ─────────────────
def resolve(host):
    try:
        return socket.getaddrinfo(host, None, proto=socket.IPPROTO_TCP)[0][4][0]
    except OSError:
        return None


def tcp_ping(c, timeout=4):
    """Задержка TCP-подключения в мс или None, если порт закрыт."""
    t = time.monotonic()
    try:
        with socket.create_connection((c["host"], c["port"]), timeout=timeout):
            return (time.monotonic() - t) * 1000
    except OSError:
        return None


def xray_config(c, port):
    """Конфиг Xray для одного сервера. None — если транспорт неизвестен."""
    q = c["q"]
    t = c["type"]
    path, host = q.get("path", ""), q.get("host", "")
    user = {"id": c["uuid"], "encryption": "none"}
    ss = {"security": "reality", "realitySettings": {
        "serverName": c["sni"], "fingerprint": q.get("fp") or "chrome",
        "publicKey": q["pbk"], "shortId": q.get("sid", ""), "spiderX": q.get("spx", "")}}
    if t in ("tcp", "raw"):
        ss["network"] = "tcp"
        if q.get("flow"):
            user["flow"] = q["flow"]
        if q.get("headertype") == "http":
            ss["tcpSettings"] = {"header": {"type": "http", "request": {
                "path": [path or "/"], "headers": {"Host": [h for h in host.split(",") if h]}}}}
    elif t == "grpc":
        ss["network"] = "grpc"
        ss["grpcSettings"] = {"serviceName": q.get("servicename", ""), "multiMode": q.get("mode") == "multi"}
    elif t in ("http", "h2"):
        ss["network"] = "h2"
        ss["httpSettings"] = {"path": path or "/", "host": [h for h in host.split(",") if h]}
    elif t in ("xhttp", "splithttp"):
        ss["network"] = "xhttp"
        xs = {"path": path or "/", "mode": q.get("mode") or "auto"}
        if host:
            xs["host"] = host
        try:
            if q.get("extra"):
                xs["extra"] = json.loads(q["extra"])
        except ValueError:
            pass
        ss["xhttpSettings"] = xs
    elif t == "ws":
        ss["network"] = "ws"
        ss["wsSettings"] = {"path": path or "/", "headers": {"Host": host} if host else {}}
    elif t == "httpupgrade":
        ss["network"] = "httpupgrade"
        ss["httpupgradeSettings"] = {"path": path or "/", "host": host}
    elif t == "kcp":
        ss["network"] = "kcp"
        ss["kcpSettings"] = {"header": {"type": q.get("headertype") or "none"}, "seed": q.get("seed", "")}
    else:
        return None
    return {
        "log": {"loglevel": "none"},
        "inbounds": [{"listen": "127.0.0.1", "port": port, "protocol": "socks", "settings": {"udp": False}}],
        "outbounds": [{"protocol": "vless", "streamSettings": ss,
                       "settings": {"vnext": [{"address": c["host"], "port": c["port"], "users": [user]}]}}],
    }


def _curl_text(port, url, timeout):
    try:
        r = subprocess.run(["curl", "-s", "-m", str(timeout), "-x", f"socks5h://127.0.0.1:{port}", url],
                           capture_output=True, text=True, timeout=timeout + 4)
        return r.stdout
    except (subprocess.TimeoutExpired, OSError):
        return ""


def _exit_info(port):
    """Через поднятый сервер спрашиваем «какой у меня IP» → (выходной IP, код страны по версии Cloudflare)."""
    for url in EXIT_URLS:
        out = _curl_text(port, url, EXIT_TIMEOUT)
        m = re.search(r"^ip=(\S+)", out, re.M) or re.match(r"^\s*([0-9a-fA-F:.]+)\s*$", out)
        if not m:
            continue
        try:
            ip = str(ipaddress.ip_address(m.group(1)))
        except ValueError:
            continue
        loc = re.search(r"^loc=([A-Z]{2})", out, re.M)
        return ip, (loc.group(1) if loc else "")
    return None, ""


def probe(c, xray_bin):
    """Поднимает сервер в Xray. Возвращает {'exit_ip', 'exit_cc', 'mbps'} или None, если сервер не работает.
    Сервер считается рабочим, если через него удалось узнать выходной IP; скорость — отдельно (0.0, если
    скачивание не удалось, например Cloudflare не пустил)."""
    port = next(_ports)
    cfg = xray_config(c, port)
    if cfg is None:
        return None
    p = None
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "c.json"
        path.write_text(json.dumps(cfg))
        try:
            p = subprocess.Popen([xray_bin, "run", "-c", str(path)],
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            for _ in range(40):  # ждём, пока Xray откроет порт (до 4 с)
                if p.poll() is not None:
                    return None
                try:
                    socket.create_connection(("127.0.0.1", port), 0.2).close()
                    break
                except OSError:
                    time.sleep(0.1)
            else:
                return None
            ip, cc = _exit_info(port)
            if not ip:
                return None
            mbps = 0.0
            try:
                r = subprocess.run(
                    ["curl", "-s", "-o", "/dev/null", "-m", str(SPEED_TIMEOUT),
                     "-x", f"socks5h://127.0.0.1:{port}",
                     "-w", "%{http_code} %{size_download} %{speed_download}", SPEED_URL],
                    capture_output=True, text=True, timeout=SPEED_TIMEOUT + 5)
                code, size, speed = r.stdout.split()
                if code == "200" and float(size) >= 50_000:
                    mbps = float(speed) * 8 / 1e6
            except (subprocess.TimeoutExpired, ValueError, OSError):
                pass
            return {"exit_ip": ip, "exit_cc": cc, "mbps": mbps}
        except OSError:
            return None
        finally:
            if p:
                p.kill()
                p.wait()


def geo_lookup(ips):
    """ip-api.com, пакеты по 100 (лимит бесплатного тарифа — 15 пакетов в минуту)."""
    res, ips = {}, sorted(ips)
    for i in range(0, len(ips), 100):
        body = json.dumps([{"query": ip, "fields": "status,country,countryCode,city,query",
                            "lang": GEO_LANG} for ip in ips[i:i + 100]]).encode()
        txt = http("http://ip-api.com/batch", headers={"Content-Type": "application/json"}, data=body)
        try:
            for r in json.loads(txt or "[]"):
                if r.get("status") == "success":
                    res[r["query"]] = r
        except ValueError:
            pass
        time.sleep(4.5)
    return res


def flag(cc):
    if not re.fullmatch(r"[A-Za-z]{2}", cc or ""):
        return "🏳"
    return "".join(chr(0x1F1E6 + ord(c) - 65) for c in cc.upper())


def make_name(g, fallback_cc=""):
    country, city = g.get("country", ""), g.get("city", "")
    if country:
        return f"{flag(g.get('countryCode', ''))} {country}" + (f", {city}" if city and city != country else "")
    if fallback_cc:  # ip-api не ответил — хотя бы страна по данным Cloudflare
        return f"{flag(fallback_cc)} {fallback_cc}"
    return "🏳 Unknown"


# ───────────────────────────── сборка списка ─────────────────────────────
def build(raw, keep_other=False, check_tcp=True, xray_bin=None, use_geo=True, stats=None,
          resolver=resolve, tcp_fn=tcp_ping, probe_fn=probe, geo_fn=geo_lookup):
    stats = stats if stats is not None else Counter()
    stats["links_found"] = len(raw)

    # 1. разбор и дедупликация
    why, cands = Counter(), {}
    for link in raw:
        c = parse_vless(link, keep_other, why)
        if not c:
            continue
        key = (c["host"], c["port"], c["uuid"], c["sni"], c["type"])
        cands.setdefault(key, c)
    cands = list(cands.values())
    stats["reality_suitable_unique"] = len(cands)
    stats["by_transport"] = dict(Counter(c["type"] for c in cands))
    stats["by_sni_tier"] = dict(Counter(c["tier"] for c in cands))

    # 2. DNS → IP
    hosts = sorted({c["host"] for c in cands})
    with cf.ThreadPoolExecutor(64) as ex:
        ip_of = dict(zip(hosts, ex.map(resolver, hosts)))
    cands = [c for c in cands if ip_of.get(c["host"])]
    for c in cands:
        c["ip"] = ip_of[c["host"]]
    stats["dns_ok"] = len(cands)

    # 3. TCP: отсев мёртвых и задержка
    if check_tcp:
        with cf.ThreadPoolExecutor(100) as ex:
            pings = list(ex.map(tcp_fn, cands))
        cands = [dict(c, ms=ms) for c, ms in zip(cands, pings) if ms is not None]
        stats["tcp_ok"] = len(cands)
    for c in cands:
        c.setdefault("ms", 0.0)
    cands.sort(key=lambda c: (c["tier"] == 0, c["ms"], c["base"]))

    # 4. проверка через Xray: рабочий ли сервер, выходной IP, скорость
    if xray_bin:
        batch = cands[:MAX_TEST]
        log(f"Проверка через Xray: {len(batch)} серверов, {SPEED_WORKERS} параллельно…")
        with cf.ThreadPoolExecutor(SPEED_WORKERS) as ex:
            res = list(ex.map(lambda c: probe_fn(c, xray_bin), batch))
        cands = [dict(c, **r) for c, r in zip(batch, res) if r]
        stats["xray_ok"] = len(cands)
        stats["xray_with_speed"] = sum(c["mbps"] > 0 for c in cands)
    cands.sort(key=lambda c: (c["tier"] == 0, -c.get("mbps", 0.0), c["ms"], c["base"]))

    # 5. лимит на адрес и общий потолок
    per_ip, final = Counter(), []
    for c in cands:
        if per_ip[c["ip"]] >= MAX_PER_IP:
            stats["dropped_per_ip_limit"] += 1
            continue
        per_ip[c["ip"]] += 1
        final.append(c)
        if len(final) >= MAX_TOTAL:
            break

    # 6. страна и город: по ВЫХОДНОМУ IP (если проверяли через Xray), иначе по адресу сервера
    ips = {c["ip"] for c in final} | {c["exit_ip"] for c in final if c.get("exit_ip")}
    geo = geo_fn(ips) if use_geo and ips else {}
    for c in final:
        place = c.get("exit_ip") or c["ip"]
        c["name"] = make_name(geo.get(place, {}), c.get("exit_cc", ""))
        c["entry_cc"] = geo.get(c["ip"], {}).get("countryCode", "")
        c["exit_country"] = geo.get(place, {}).get("countryCode", "") or c.get("exit_cc", "")
    stats["final"] = len(final)
    stats["final_entry_in_ru"] = sum(c["entry_cc"] == "RU" for c in final)
    stats["final_exit_in_ru"] = sum(c["exit_country"] == "RU" for c in final)
    for k, v in why.items():
        stats[f"drop_{k}"] = v
    return final, stats


def write_outputs(final, stats):
    OUT.mkdir(exist_ok=True)
    line = lambda c: f"{c['base']}#{up.quote(c['name'])}"
    allp = "\n".join(line(c) for c in final) + "\n"
    (OUT / "whitelist_ru_sni.txt").write_text(allp, encoding="utf-8")
    (OUT / "whitelist_ru_sni_b64.txt").write_text(base64.b64encode(allp.encode()).decode(), encoding="utf-8")
    ru = "\n".join(line(c) for c in final if c["entry_cc"] == "RU")
    (OUT / "whitelist_ru_sni_ruip.txt").write_text(ru + "\n" if ru else "", encoding="utf-8")
    (OUT / "report.txt").write_text("\n".join(f"{k}: {v}" for k, v in stats.items()) + "\n", encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--xray", help="путь к бинарнику xray (или переменная XRAY_BIN)")
    ap.add_argument("--no-speed", action="store_true", help="не запускать Xray (имена тогда по адресу сервера, не по выходу!)")
    ap.add_argument("--no-tcp", action="store_true", help="не делать TCP-проверку")
    ap.add_argument("--no-geo", action="store_true", help="не определять страну по IP")
    ap.add_argument("--keep-other", action="store_true", help="добирать Reality и с нероссийским SNI (в конец списка)")
    ap.add_argument("--skip-github-search", action="store_true", help="не искать на GitHub (только repo:/url:/tg:)")
    args = ap.parse_args()

    xray_bin = None
    if not args.no_speed:
        found = shutil.which(args.xray or os.environ.get("XRAY_BIN") or "xray")
        if not found:
            log("! xray не найден — имена будут по адресу сервера, а не по выходному IP")
        elif not shutil.which("curl"):
            log("! curl не найден — имена будут по адресу сервера, а не по выходному IP")
        else:
            xray_bin = str(Path(found).resolve())

    token = os.environ.get("GH_SEARCH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    src = load_sources()
    stats = Counter()
    urls = list(src["url"])
    raw = []

    for repo in src["repo"]:
        found = repo_file_urls(repo, token, FILES_PER_REPO)
        log(f"repo {repo}: файлов {len(found)}")
        urls += found
    stats["repos_manual"] = len(src["repo"])

    if not args.skip_github_search:
        if not token:
            log("! нет GITHUB_TOKEN — поиск по GitHub пропущен")
        else:
            skip = {r.lower() for r in src["repo"]}
            repos = discover_repos(src["discover"], token, skip)
            stats["repos_discovered"] = len(repos)
            with cf.ThreadPoolExecutor(4) as ex:
                for found in ex.map(lambda r: repo_file_urls(r, token, FILES_PER_FOUND), repos):
                    urls += found
            urls += gh_search_files(src["search"], token)

    urls = list(dict.fromkeys(urls))
    stats["files_to_download"] = len(urls)
    log(f"Скачиваю {len(urls)} файлов…")
    with cf.ThreadPoolExecutor(16) as ex:
        for txt in ex.map(http, urls):
            if txt:
                stats["files_downloaded"] += 1
                raw += extract_links(txt)
    stats["links_from_files"] = len(raw)

    for ch in src["tg"]:
        got = fetch_tg(ch)
        log(f"tg {ch}: ссылок {len(got)}")
        raw += got
    stats["tg_channels"] = len(src["tg"])
    stats["links_from_tg"] = len(raw) - stats["links_from_files"]

    final, stats = build(raw, args.keep_other, not args.no_tcp, xray_bin, not args.no_geo, stats)
    write_outputs(final, stats)
    log("Итого:\n" + "\n".join(f"  {k}: {v}" for k, v in stats.items()))
    if not final:
        log("! ничего не найдено — файлы перезаписаны пустыми, смотри out/report.txt и sources.txt")


if __name__ == "__main__":
    main()
