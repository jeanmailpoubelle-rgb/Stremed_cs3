// ==UserScript==
// @name         Cloudstream Media Finder
// @namespace    local.cloudstream.media.finder
// @version      1.8.0
// @updateURL    https://raw.githubusercontent.com/jeanmailpoubelle-rgb/Stremed_cs3/main/cloudstream-media-finder.user.js
// @downloadURL  https://raw.githubusercontent.com/jeanmailpoubelle-rgb/Stremed_cs3/main/cloudstream-media-finder.user.js
// @description  Play browser-discovered media in Cloudstream. Smart source selection, Copy redirect link, subtitle handoff, and optional playback settings.
// @match        http://*/*
// @match        https://*/*
// @run-at       document-start
// @grant        none
// @sandbox      raw
// ==/UserScript==

(() => {
  'use strict';
  const CHANNEL = 'cloudstream-media-finder/1';
  const FINDER_VERSION = '1.8.0';
  const LIMIT = 150;
  const items = new Map();
  const refererOverrides = new Map();
  const playbackOverrides = new Map();
  const cards = new Map();
  const clearKeys = new Map();
  const playerClearKeys = new Map();
  const emeHooks = [];
  const segmentUrls = new Set();
  const dashRules = new Map();
  const sourceSubtitles = new Map();
  const nonSubtitleUrls = new Set();
  const subtitleObservations = new Map();
  const configuredCaptionSources = new Set();
  const domCaptionOwners = new WeakMap();
  const subtitlePlaylists = new Set();
  const redirectAliases = new Map();
  const blobSources = new WeakMap();
  const blobUrls = new Map();
  const playlistParents = new Map();
  const MAX_TEXT_BYTES = 262144;
  let pendingInspections = 0;
  let showAll = false;
  const mediaRoots = new Set();
  const observableHeaders = new Set(['accept', 'accept-language', 'x-requested-with']);
  const reservedHeaders = new Set(['referer', 'user-agent', 'origin', 'host', 'connection', 'content-length',
    'content-type', 'transfer-encoding', 'accept-encoding', 'range', 'if-range', 'te', 'trailer', 'upgrade', 'keep-alive']);
  const isTop = window === window.top;
  let ui;
  let renderPending = false;
  const extensionTypes = { m3u8: 'HLS', mpd: 'DASH', mp4: 'MP4', webm: 'WebM', m4v: 'Video', mov: 'Video', mkv: 'Video', ogv: 'Video', mp3: 'Audio', m4a: 'Audio', ogg: 'Audio', wav: 'Audio', flac: 'Audio', opus: 'Audio' };

  function httpUrl(value) {
    try {
      const url = new URL(String(value), location.href);
      return ['http:', 'https:'].includes(url.protocol) && !url.username && !url.password ? url.href : null;
    } catch { return null; }
  }

  function mediaType(url, mime = '', videoElement = false) {
    try {
      const path = new URL(url).pathname;
      // Segments are not standalone streams; do not flood the list with them.
      if (/\.(ts|m4s|vtt|srt|jpg|png|gif)$/i.test(path)) return null;
      const ext = /\.([a-z0-9]+)$/i.exec(path)?.[1].toLowerCase();
      // Response MIME is stronger evidence than a filename or DOM guess.
      if (/mpegurl/i.test(mime)) return { kind: 'HLS', confidence: 3 };
      if (/dash\+xml/i.test(mime)) return { kind: 'DASH', confidence: 3 };
      if (/^video\/(mp4|webm|quicktime|x-m4v)(?:;|$)/i.test(mime)) return { kind: ext === 'mp4' ? 'MP4' : ext === 'webm' ? 'WebM' : 'Video', confidence: 3 };
      if (/^video\/(x-matroska|ogg)(?:;|$)/i.test(mime)) return { kind: 'Video', confidence: 3 };
      if (/^audio\/(mpeg|mp4|ogg|wav|x-wav|flac|x-flac|opus)(?:;|$)/i.test(mime)) return { kind: 'Audio', confidence: 3 };
      if (extensionTypes[ext]) return { kind: extensionTypes[ext], confidence: 2 };
      return videoElement ? { kind: 'Video element', confidence: 1 } : null;
    } catch { return null; }
  }

  function record(value, method, mime = '', status = null, videoElement = false, context = {}) {
    const url = httpUrl(value);
    if (!url || isSegment(url) || subtitlePlaylists.has(url)) return;
    const alias = redirectAliases.get(url);
    if (alias && items.has(alias) && (status === null || status >= 200 && status < 300)) return;
    const media = mediaType(url, mime, videoElement);
    if (!media) return;
    const contentIssue = /response|destination/i.test(method) && status >= 200 && status < 300 ? (/text\/html|application\/xhtml/i.test(mime) ? 'html' : '') : undefined;
    publish({ subtitles: sourceSubtitles.get(url), ...context, ...media, ...(contentIssue === undefined ? {} : { contentIssue }), confidence: context.confidence || media.confidence,
      url, method, page: location.href, status, browserAgent: navigator.userAgent,
      title: context.title || document.title });
    if (subtitleObservations.size) queueMicrotask(reconcileSubtitles);
  }

  // Observe only standard ClearKey JWKs that the player successfully supplied
  // to EME. Never inspect Widevine license bytes or extract device/session keys.
  function canonicalKey(value) {
    if (typeof value !== 'string' || !/^[A-Za-z0-9_-]{21}[AQgw]$/.test(value)) return null;
    return value;
  }

  function kidFromUuid(value) {
    if (!/^[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}$/i.test(value)) return null;
    const bytes = value.replace(/-/g, '').match(/../g).map(v => parseInt(v, 16));
    return btoa(String.fromCharCode(...bytes)).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }

  function matchingClearKey(kids, url) {
    // Cloudstream's LocalMediaDrmCallback accepts one key. Do not choose an
    // arbitrary key for multi-key manifests or guess from a different video.
    if (kids?.length !== 1) return null;
    const configured = playerClearKeys.get(url)?.get(kids[0]);
    const key = configured || clearKeys.get(kids[0]);
    return key ? { kid: kids[0], key } : null;
  }

  function observeClearKeys(input) {
    try {
      let bytes;
      if (input instanceof ArrayBuffer) bytes = new Uint8Array(input);
      else if (ArrayBuffer.isView(input)) bytes = new Uint8Array(input.buffer, input.byteOffset, input.byteLength);
      if (!bytes || bytes.byteLength > 16384) return;
      const json = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes));
      if (!Array.isArray(json.keys) || json.keys.length > 32) return;
      for (const entry of json.keys) {
        if (entry?.kty !== 'oct' || !canonicalKey(entry.kid) || !canonicalKey(entry.k)) continue;
        clearKeys.set(entry.kid, entry.k);
        if (clearKeys.size > 64) clearKeys.delete(clearKeys.keys().next().value);
      }
      for (const item of items.values()) if (item.page === location.href && item.requiredKids?.length) {
        publish({ ...item, clearKey: matchingClearKey(item.requiredKids, item.url) });
      }
    } catch { /* preserve original EME behavior; non-JWK licenses remain private */ }
  }

  try {
    const clearMediaKeys = new WeakSet(), clearSessions = new WeakSet();
    const accessProto = window.MediaKeySystemAccess?.prototype;
    const keysProto = window.MediaKeys?.prototype;
    const proto = window.MediaKeySession?.prototype;
    if (typeof accessProto?.createMediaKeys === 'function' && typeof keysProto?.createSession === 'function' && typeof proto?.update === 'function') {
      const createKeys = accessProto.createMediaKeys, createSession = keysProto.createSession;
      accessProto.createMediaKeys = function (...args) {
        const isClearKey = this.keySystem === 'org.w3.clearkey';
        const result = createKeys.apply(this, args);
        if (isClearKey) Promise.resolve(result).then(keys => clearMediaKeys.add(keys), () => {});
        return result;
      };
      keysProto.createSession = function (...args) {
        const session = createSession.apply(this, args);
        if (clearMediaKeys.has(this)) clearSessions.add(session);
        return session;
      };
      const update = proto.update;
      proto.update = function (input, ...rest) {
        if (!clearSessions.has(this)) return update.call(this, input, ...rest);
        // Copy bounded configuration before the player can reuse its buffer.
        let snapshot;
        try {
          if (input instanceof ArrayBuffer && input.byteLength <= 16384) snapshot = input.slice(0);
          else if (ArrayBuffer.isView(input) && input.byteLength <= 16384)
            snapshot = input.buffer.slice(input.byteOffset, input.byteOffset + input.byteLength);
        } catch { /* observation is optional */ }
        const result = update.call(this, input, ...rest);
        // Keep the original promise and its resolve/reject behavior intact.
        if (snapshot) Promise.resolve(result).then(() => observeClearKeys(snapshot), () => {});
        return result;
      };
      emeHooks.push([accessProto, 'createMediaKeys', accessProto.createMediaKeys],
        [keysProto, 'createSession', keysProto.createSession], [proto, 'update', proto.update]);
    }
  } catch { /* unavailable or non-writable EME API */ }

  function resolveUrl(value, base) {
    try { return httpUrl(new URL(value, base).href); } catch { return null; }
  }

  function score(item) {
    let value = item.active ? 180 : 0;
    if (item.manifest === 'master') value += 100;
    if (item.manifest === 'media' || item.manifest === 'dash') value += 30;
    if (item.status >= 200 && item.status < 400) value += 25;
    if (item.kind === 'HLS' || item.kind === 'DASH') value += 15;
    value += item.confidence * 4;
    if (item.status >= 400) value -= 220;
    if (item.requestMethod !== 'GET') value -= 150;
    if (item.contentIssue) value -= 220;
    if (item.drm && !item.clearKey) value -= 200;
    // A playing variant makes its master a useful adaptive source as well.
    for (const [url, parent] of playlistParents) {
      if (parent === item.url && items.get(url)?.active) { value += 180; break; }
    }
    return value;
  }

  function inferredReferer(target, source = location.href, policy = '') {
    try {
      if (source === '') return '';
      if (source === 'about:client' || !source) source = location.href;
      const page = new URL(source); page.hash = '';
      const destination = new URL(target, location.href);
      const same = page.origin === destination.origin;
      const downgrade = page.protocol === 'https:' && destination.protocol === 'http:';
      switch (policy.toLowerCase()) {
        case 'no-referrer': return '';
        case 'same-origin': return same ? page.href : '';
        case 'origin': return page.origin + '/';
        case 'strict-origin': return downgrade ? '' : page.origin + '/';
        case 'origin-when-cross-origin': return same ? page.href : page.origin + '/';
        case 'strict-origin-when-cross-origin': return downgrade ? '' : same ? page.href : page.origin + '/';
        case 'no-referrer-when-downgrade': return downgrade ? '' : page.href;
        case 'unsafe-url': return page.href;
        default: return downgrade ? '' : same ? page.href : page.origin + '/';
      }
    } catch { return location.href; }
  }

  function documentPolicy() {
    return document.querySelector('meta[name="referrer" i]')?.content || '';
  }

  function inferredOrigin(target, mode = 'cors', method = 'GET') {
    try {
      if (mode === 'no-cors' || mode === 'navigate') return '';
      if (new URL(target, location.href).origin !== location.origin && mode !== 'same-origin' ||
          !['GET', 'HEAD'].includes(String(method).toUpperCase())) {
        return window.origin === 'null' ? 'null' : location.origin;
      }
    } catch { /* unavailable request context */ }
    return '';
  }

  function forgetSegment(url) {
    segmentUrls.add(url);
    if (segmentUrls.size > 2000) segmentUrls.delete(segmentUrls.values().next().value);
    items.delete(url); refererOverrides.delete(url); playbackOverrides.delete(url); subtitleObservations.delete(url);
    if (!isTop) window.top.postMessage({ channel: CHANNEL, type: 'segment', url }, '*');
    if (isTop) scheduleRender();
  }

  function linkParent(url, parent) {
    if (url === parent) return;
    playlistParents.set(url, parent);
    const tracks = sourceSubtitles.get(url);
    if (tracks?.length && !subtitlePlaylists.has(url)) attachSubtitles(parent, tracks);
    if (playlistParents.size > 512) playlistParents.delete(playlistParents.keys().next().value);
    if (!isTop) window.top.postMessage({ channel: CHANNEL, type: 'parent', url, parent }, '*');
    if (isTop) scheduleRender();
  }

  function isSegment(url) {
    return segmentUrls.has(url) || [...dashRules.values()].some(rule => rule.test(url));
  }

  function addDashRule(template, fromFrame = false) {
    if (typeof template !== 'string' || template.length > 16384 || !httpUrl(template)) return;
    // Only fixed DASH template placeholders become regex; all website text is
    // escaped. No arbitrary regex is accepted over the frame messaging channel.
    const token = /\$(Number|Time|Bandwidth|RepresentationID)(?:%0\d{1,2}d)?\$|\$\$/g;
    const escape = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    let pattern = '^', last = 0, match;
    while ((match = token.exec(template))) {
      pattern += escape(template.slice(last, match.index));
      pattern += match[0] === '$$' ? '\\$' : match[1] === 'RepresentationID' ? '[^/?&#]{1,200}' : '[0-9]{1,24}';
      last = token.lastIndex;
    }
    pattern += escape(template.slice(last)) + '$';
    if (dashRules.has(template)) return;
    dashRules.set(template, new RegExp(pattern));
    if (dashRules.size > 256) dashRules.delete(dashRules.keys().next().value);
    for (const url of items.keys()) if (isSegment(url)) {
      items.delete(url); refererOverrides.delete(url); playbackOverrides.delete(url);
    }
    if (!isTop && !fromFrame) window.top.postMessage({ channel: CHANNEL, type: 'dashRule', template }, '*');
    if (isTop) scheduleRender();
  }

  function inspectDashSegments(xml, base) {
    let visited = 0;
    const children = (element, name) => [...element.children].filter(e => e.localName === name);
    function walk(element, inheritedBases, inheritedTemplate, inheritedList) {
      if (++visited > 2000) return;
      const localBases = children(element, 'BaseURL');
      const bases = localBases.length ? inheritedBases.flatMap(b => localBases.slice(0, 8)
        .map(e => resolveUrl(e.textContent.trim(), b)).filter(Boolean)).slice(0, 8) : inheritedBases;
      const ownTemplate = children(element, 'SegmentTemplate')[0];
      const template = { ...inheritedTemplate };
      if (ownTemplate) for (const name of ['media', 'initialization']) {
        if (ownTemplate.hasAttribute(name)) template[name] = ownTemplate.getAttribute(name);
      }
      const list = children(element, 'SegmentList')[0] || inheritedList;
      if (element.localName === 'Representation') {
        const values = { RepresentationID: element.getAttribute('id'), Bandwidth: element.getAttribute('bandwidth') };
        for (const b of bases) {
          for (const raw of Object.values(template)) {
            const substituted = raw.replace(/\$(RepresentationID|Bandwidth)(?:%0(\d{1,2})d)?\$/g,
              (token, name, digits) => values[name] ? digits ? values[name].padStart(Number(digits), '0') : values[name] : token);
            const url = resolveUrl(substituted, b); if (url && url !== base) addDashRule(url);
          }
          if (list) {
            for (const e of [...list.children].slice(0, 2000)) {
              const raw = e.localName === 'Initialization' ? e.getAttribute('sourceURL') : e.localName === 'SegmentURL' ? e.getAttribute('media') : '';
              const url = raw && resolveUrl(raw, b); if (url && url !== base) addDashRule(url);
            }
          }
          if (!Object.keys(template).length && !list && localBases.length && b !== base) addDashRule(b);
        }
      }
      for (const e of element.children) if (['Period', 'AdaptationSet', 'Representation'].includes(e.localName)) walk(e, bases, template, list);
    }
    walk(xml.documentElement, [base], {}, null);
  }

  function subtitleUrl(value, base = location.href) {
    const blob = blobUrls.get(String(value));
    return blob ? blob.url : resolveUrl(value, base);
  }

  function subtitleFormat(hint = '', url = '') {
    hint = String(hint).toLowerCase();
    if (/vtt/.test(hint)) return 'vtt';
    if (/ttml|dfxp/.test(hint)) return 'ttml';
    if (/subrip|srt/.test(hint)) return 'srt';
    if (/^(?:text\/|application\/)?(?:x-)?ass$/.test(hint)) return 'ass';
    if (/^(?:text\/|application\/)?(?:x-)?ssa$/.test(hint)) return 'ssa';
    try {
      const ext = new URL(url).pathname.split('.').pop().toLowerCase();
      return ['vtt', 'srt', 'ass', 'ssa', 'ttml'].includes(ext) ? ext : '';
    } catch { return ''; }
  }

  function subtitleLabel(value) {
    const explicit = value.label || value.name;
    const language = value.srclang || value.lang || value.language;
    let name = explicit || language || 'Subtitles';
    if (!explicit && /^[a-z]{2,3}(?:-[a-z0-9]{2,8})*$/i.test(String(language || ''))) {
      try { name = new Intl.DisplayNames(['en'], { type: 'language' }).of(language) || language; } catch {}
    }
    return String(name).replace(/[\u0000-\u001f\u007f]/g, ' ').slice(0, 120) || 'Subtitles';
  }

  function subtitleTrack(value, base = location.href, context = {}) {
    if (!value || typeof value !== 'object' || !['subtitles', 'captions', 'subtitle', 'caption', ''].includes(String(value.kind || '').toLowerCase())) return null;
    const url = subtitleUrl(value.file || value.src || value.url || '', base);
    const hint = value.format || value.type || value.subtitleMime;
    const format = subtitleFormat(hint, url);
    if (!url || nonSubtitleUrls.has(url) || !format && !value.subtitleMime && !['subtitles', 'captions', 'subtitle', 'caption'].includes(String(value.kind).toLowerCase())) return null;
    const observed = subtitleObservations.get(url);
    const actual = observed?.track || {};
    const headers = configuredHeaders(context.requestHeaders || value.headers || actual.headers);
    return { url, name: subtitleLabel(value), format: hint ? format : actual.format || format,
      referer: context.suggestedReferer ?? actual.referer ?? inferredReferer(url, location.href, documentPolicy()),
      ua: navigator.userAgent, origin: context.suggestedOrigin ?? actual.origin ?? inferredOrigin(url),
      ...(Object.keys(headers).length ? { headers } : {}) };
  }

  function cleanSubtitles(rows) {
    const seen = new Set(), result = [];
    for (const row of Array.isArray(rows) ? rows.slice(0, 40) : []) {
      const url = row && httpUrl(row.url);
      if (!url || url.length > 8192 || seen.has(url) || typeof row.name !== 'string' || isSegment(url) || nonSubtitleUrls.has(url)) continue;
      const name = row.name.replace(/[\u0000-\u001f\u007f]/g, ' ').slice(0, 120) || 'Subtitles';
      const referer = typeof row.referer === 'string' && (row.referer === '' || httpUrl(row.referer)) ? row.referer : '';
      const ua = typeof row.ua === 'string' && row.ua.length <= 1024 && !/[\u0000-\u001f\u007f]/.test(row.ua) ? row.ua : '';
      const origin = typeof row.origin === 'string' && (['', 'null'].includes(row.origin) || httpUrl(row.origin) && new URL(row.origin).origin === row.origin) ? row.origin : '';
      const format = ['', 'vtt', 'srt', 'ttml', 'ass', 'ssa'].includes(row.format) ? row.format : '';
      const headers = configuredHeaders(row.headers);
      seen.add(url); result.push({ url, name, referer, ua, origin, format, ...(Object.keys(headers).length ? { headers } : {}) });
      if (result.length === 20) break;
    }
    return result;
  }

  function rootSource(value) {
    let url = value; const seen = new Set();
    for (let i = 0; i < 8 && !seen.has(url); i++) {
      seen.add(url);
      const parent = redirectAliases.get(url) || playlistParents.get(url);
      if (!parent || !items.has(parent) || items.get(parent).status >= 400) break;
      url = parent;
    }
    return url;
  }

  function attachSubtitles(url, tracks, replace = false, propagate = true) {
    const clean = cleanSubtitles(tracks);
    if (!clean.length && !replace || isSegment(url) || subtitlePlaylists.has(url)) return;
    const old = sourceSubtitles.get(url) || [];
    const labelled = clean.map(row => row.name === 'Subtitles' ? { ...old.find(o => o.url === row.url), ...row,
      name: old.find(o => o.url === row.url)?.name || row.name } : row);
    const combined = replace ? labelled : cleanSubtitles([...labelled, ...old]);
    if (JSON.stringify(combined) !== JSON.stringify(old)) {
      sourceSubtitles.set(url, combined);
      if (sourceSubtitles.size > LIMIT) sourceSubtitles.delete(sourceSubtitles.keys().next().value);
      const item = items.get(url);
      if (item) publish({ ...item, subtitles: combined });
    }
    // Captions attached to a selected variant/redirect also belong to the
    // discovered master. Preserve that master so native HLS text renditions work.
    const parent = rootSource(url);
    if (propagate && parent !== url) attachSubtitles(parent, combined, replace, false);
  }

  function currentFrameSources() {
    const unique = new Map();
    for (const item of items.values()) if (item.page === location.href && !isSegment(item.url) && !subtitlePlaylists.has(item.url) &&
      (item.status === null || item.status >= 200 && item.status < 400) && item.requestMethod === 'GET' && item.kind !== 'Audio') {
      const url = rootSource(item.url);
      unique.set(url, items.get(url) || item);
    }
    return [...unique.values()];
  }

  function reconcileSubtitles() {
    const sources = currentFrameSources();
    if (sources.length !== 1 || configuredCaptionSources.has(sources[0].url)) return;
    for (const [url, observation] of subtitleObservations) if (observation.verified && !nonSubtitleUrls.has(url) &&
      !isSegment(url) && Date.now() - observation.time < 120000) attachSubtitles(sources[0].url, [observation.track]);
  }

  function observeSubtitle(value, mime = '', status = null, context = {}, verified = false) {
    if (status !== null && (status < 200 || status >= 400) || context.requestMethod && context.requestMethod !== 'GET') return;
    const url = httpUrl(value);
    if (!url || isSegment(url) || nonSubtitleUrls.has(url) || /(?:thumb(?:nails?)?|sprite|storyboard|chapters?)[^/]*\.(?:vtt|srt)/i.test(new URL(url).pathname)) return;
    const format = subtitleFormat(mime, url);
    if (!format) return;
    const track = subtitleTrack({ url, label: 'Subtitles', subtitleMime: mime, format }, location.href, context);
    if (!track) return;
    const old = subtitleObservations.get(url);
    subtitleObservations.set(url, { track, verified: verified || old?.verified || false, time: Date.now() });
    if (subtitleObservations.size > 80) subtitleObservations.delete(subtitleObservations.keys().next().value);
    // Update exact configured ownership even when other same-page videos exist.
    for (const [source, tracks] of sourceSubtitles) if (tracks.some(t => t.url === url)) {
      attachSubtitles(source, tracks.map(t => t.url === url ? { ...t, ...track, name: t.name } : t), true);
    }
    reconcileSubtitles();
  }

  function trackRows(value) {
    if (Array.isArray(value)) return value.slice(0, 40);
    if (value && typeof value === 'object') return Object.entries(value).slice(0, 40)
      .map(([lang, row]) => typeof row === 'string' ? { file: row, lang } : { lang, ...row });
    return [];
  }

  function objectSubtitles(node, base) {
    const rows = [...trackRows(node.tracks), ...trackRows(node.subtitles).map(v => ({ ...v, kind: v?.kind || 'subtitles' })),
      ...trackRows(node.captions).map(v => ({ ...v, kind: v?.kind || 'captions' }))];
    for (const track of rows) if (track?.kind && !['subtitles', 'captions', 'subtitle', 'caption'].includes(String(track.kind).toLowerCase())) {
      const url = subtitleUrl(track.file || track.src || track.url || '', base);
      if (url) {
        nonSubtitleUrls.add(url); subtitleObservations.delete(url);
        if (nonSubtitleUrls.size > 100) nonSubtitleUrls.delete(nonSubtitleUrls.values().next().value);
      }
    }
    const tracks = rows.slice(0, 40).map(v => subtitleTrack(v, base)).filter(Boolean);
    if (!rows.length && !('tracks' in node) && !('subtitles' in node) && !('captions' in node)) return;
    const media = Array.isArray(node.sources) ? node.sources.slice(0, 40) : typeof node.sources === 'string' ? [node.sources] : [node];
    for (const source of media) {
      const raw = typeof source === 'string' ? source : source?.file || source?.src || source?.url || source?.contentUrl;
      const url = raw && resolveUrl(raw, base);
      const hint = source?.type || source?.mimeType || '';
      const mime = /^(hls|m3u8)$/i.test(hint) ? 'application/vnd.apple.mpegurl' : /^(dash|mpd)$/i.test(hint) ? 'application/dash+xml' : hint;
      if (url && mediaType(url, mime)) {
        configuredCaptionSources.add(url); configuredCaptionSources.add(rootSource(url));
        if (configuredCaptionSources.size > LIMIT * 2) configuredCaptionSources.delete(configuredCaptionSources.values().next().value);
        attachSubtitles(url, tracks, true);
      }
    }
  }

  function scanPlayerTracks() {
    // Only existing public read-only player getters; never setup/load/play.
    const videos = queryMediaRoots('video, audio');
    const players = new Set([window.player, window.hls]);
    for (const video of videos) for (const player of [video.player, video.hls, video.plyr]) if (player) players.add(player);
    try {
      if (typeof window.videojs?.getAllPlayers === 'function') for (const player of window.videojs.getAllPlayers().slice(0, 8)) players.add(player);
      if (typeof window.jwplayer === 'function') for (const e of queryMediaRoots('.jwplayer[id]').slice(0, 8)) players.add(window.jwplayer(e.id));
    } catch {}
    for (const player of [...players].slice(0, 16)) if (player) try {
      scanConfiguredClearKeys(player);
      if (typeof player.getPlaylistItem === 'function') inspectObject(player.getPlaylistItem(), document.baseURI);
      if (typeof player.currentSource === 'function' && typeof player.remoteTextTracks === 'function') {
        const source = player.currentSource(), tracks = player.remoteTextTracks();
        const rows = Array.from({ length: Math.min(Number(tracks?.length) || 0, 40) }, (_, i) => tracks[i]);
        objectSubtitles({ sources: [source], tracks: rows }, document.baseURI);
        const elements = typeof player.remoteTextTrackEls === 'function' ? player.remoteTextTrackEls() : null;
        for (let i = 0; i < Math.min(Number(elements?.length) || 0, 40); i++) {
          const el = elements[i], t = subtitleTrack({ src: el?.src, kind: el?.kind || 'subtitles', label: el?.label, srclang: el?.srclang });
          const url = source && resolveUrl(source.src || source.url, document.baseURI);
          if (url && t) attachSubtitles(url, [t]);
        }
      }
      // Hls.js exposes the manifest URL and text rendition URLs. Those HLS
      // playlists stay inside the master, rather than becoming external VTT files.
      if (typeof player.url === 'string' && player.media && Array.isArray(player.subtitleTracks)) {
        record(player.url, 'Existing HLS player', 'application/vnd.apple.mpegurl');
        for (const track of player.subtitleTracks.slice(0, 40)) for (const raw of typeof track.url === 'string' ? [track.url] : Array.isArray(track.url) ? track.url : []) {
          const url = resolveUrl(raw, player.url); if (url) markSubtitlePlaylist(url);
        }
        const dom = domTracks(player.media);
        if (dom.length) attachSubtitles(httpUrl(player.url), dom, true);
      }
      const source = player.source;
      if (source && typeof source === 'object' && (Array.isArray(source.sources) || source.src)) inspectObject(source, document.baseURI);
    } catch { /* one unsupported player must not stop the others */ }
  }

  function markSubtitlePlaylist(url) {
    subtitlePlaylists.add(url);
    if (subtitlePlaylists.size > 100) subtitlePlaylists.delete(subtitlePlaylists.values().next().value);
    items.delete(url); sourceSubtitles.delete(url);
    if (!isTop) window.top.postMessage({ channel: CHANNEL, type: 'subtitlePlaylist', url }, '*');
    if (isTop) scheduleRender();
  }

  function configurationKey(value) {
    if (canonicalKey(value)) return value;
    if (typeof value !== 'string' || !/^[a-f0-9]{32}$/i.test(value)) return null;
    return btoa(String.fromCharCode(...value.match(/../g).map(v => parseInt(v, 16))))
      .replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }

  function scanConfiguredClearKeys(player) {
    // Existing players' public configuration is a fallback when a polyfill or
    // late script injection replaced the EME observers. Never start a player,
    // evaluate its scripts, or inspect other DRM systems/licence responses.
    try {
      let url, pairs;
      if (typeof player?.getAssetUri === 'function' && typeof player?.getConfiguration === 'function') {
        const asset = player.getAssetUri();
        url = typeof asset === 'string' && asset ? httpUrl(asset) : null;
        const config = player.getConfiguration();
        if (config?.drm?.clearKeys && typeof config.drm.clearKeys === 'object')
          pairs = Object.entries(config.drm.clearKeys).slice(0, 32);
        else pairs = [];
      } else if (typeof player?.getPlaylistItem === 'function') {
        const entry = player.getPlaylistItem();
        const sources = Array.isArray(entry?.sources) ? entry.sources.slice(0, 40) : [entry];
        for (const source of sources) {
          const key = source?.drm?.clearkey || entry?.drm?.clearkey;
          const raw = source?.file || source?.src || source?.url;
          const target = typeof raw === 'string' && raw ? resolveUrl(raw, document.baseURI) : null;
          if (target && key) storeConfiguredKeys(target, [[key.keyId, key.key]]);
        }
        return;
      }
      if (url && pairs) storeConfiguredKeys(url, pairs);
    } catch { /* read-only observation must not change the website */ }
  }

  function storeConfiguredKeys(url, pairs) {
    const keys = new Map();
    for (const [rawKid, rawKey] of pairs) {
      const kid = configurationKey(rawKid), key = configurationKey(rawKey);
      if (kid && key) keys.set(kid, key);
    }
    if (keys.size) playerClearKeys.set(url, keys);
    else playerClearKeys.delete(url);
    if (playerClearKeys.size > 64) playerClearKeys.delete(playerClearKeys.keys().next().value);
    const item = items.get(url);
    // A configured key still requires exact source URL + verified single KID.
    // Public configuration alone does not establish that a manifest is valid.
    if (item?.page === location.href && item.requiredKids?.length)
      publish({ ...item, clearKey: matchingClearKey(item.requiredKids, url) });
  }

  function domTracks(video) {
    return [...video.querySelectorAll('track[kind="subtitles"], track[kind="captions"], track:not([kind])')]
      .map(e => subtitleTrack({ src: e.src, label: e.label, srclang: e.srclang, kind: e.kind })).filter(Boolean);
  }

  function scanSubtitleTracks() {
    const videos = queryMediaRoots('video, audio');
    for (const video of videos) {
      const tracks = domTracks(video);
      const direct = httpUrl(video.currentSrc || video.src);
      const sources = !direct && videos.length === 1 ? currentFrameSources() : [];
      const owner = direct || (sources.length === 1 ? sources[0].url : null);
      if (owner && (tracks.length || domCaptionOwners.get(video) === owner)) {
        configuredCaptionSources.add(owner); configuredCaptionSources.add(rootSource(owner));
        if (configuredCaptionSources.size > LIMIT * 2) configuredCaptionSources.delete(configuredCaptionSources.values().next().value);
        domCaptionOwners.set(video, owner);
        attachSubtitles(owner, tracks, true);
      }
    }
    reconcileSubtitles();
  }

  function inspectObject(value, base) {
    const stack = [value]; let visited = 0, found = 0;
    while (stack.length && visited++ < 5000 && found < 40) {
      const node = stack.pop();
      if (typeof node === 'string') {
        if (node.length <= 16384 && /\.(m3u8|mpd|mp4|webm|m4v|mov|mkv|ogv|mp3|m4a|ogg|wav|flac|opus)(?:[?#]|$)/i.test(node)) {
          const url = resolveUrl(node, base);
          if (url) { record(url, 'Available player source'); found++; }
        }
      } else if (Array.isArray(node)) {
        for (let i = Math.min(node.length, 5000) - 1; i >= 0; i--) stack.push(node[i]);
      } else if (node && typeof node === 'object') {
        objectSubtitles(node, base);
        const hint = typeof node.type === 'string' ? node.type : typeof node.mimeType === 'string' ? node.mimeType : '';
        const hintMime = /^(hls|m3u8)$/i.test(hint) ? 'application/vnd.apple.mpegurl' : /^(dash|mpd)$/i.test(hint) ? 'application/dash+xml' : hint;
        for (const [key, child] of Object.entries(node).slice(0, 5000)) {
          if (typeof child === 'string' && /^(file|src|url|contentUrl|playbackUrl)$/i.test(key) && /mpegurl|dash\+xml|^(video|audio)\//i.test(hintMime)) {
            const url = resolveUrl(child, base);
            if (url) { record(url, 'Available player source', hintMime); found++; }
          } else stack.push(child);
          if (found >= 40) break;
        }
      }
    }
  }

  function inspectText(text, base, context = {}, status = null) {
    if (typeof text !== 'string' || text.length > MAX_TEXT_BYTES) return;
    if (/^\s*#EXTM3U(?:\s|$)/.test(text)) {
      const master = /#EXT-X-STREAM-INF:/.test(text);
      let variants = 0, next = '';
      for (const raw of text.split(/\r?\n/)) {
        const line = raw.trim();
        if (/^#EXT-X-STREAM-INF:/.test(line)) { next = 'variant'; continue; }
        if (/^#EXTINF:/.test(line)) { next = 'segment'; continue; }
        if (/^#EXT-X-MAP:/.test(line)) {
          const uri = /\bURI="([^"]+)"/.exec(line)?.[1];
          const url = uri && resolveUrl(uri, base); if (url) forgetSegment(url);
        }
        if (/^#EXT-X-MEDIA:/.test(line)) {
          const uri = /\bURI="([^"]+)"/.exec(line)?.[1];
          const url = uri && resolveUrl(uri, base);
          if (url && /(?:^|,)TYPE=SUBTITLES(?:,|$)/.test(line.substring(line.indexOf(':') + 1))) markSubtitlePlaylist(url);
          else if (url) linkParent(url, base);
        }
        if (/^#EXT-X-(?:PART|PRELOAD-HINT|KEY):/.test(line)) {
          const uri = /\bURI="([^"]+)"/.exec(line)?.[1];
          const url = uri && resolveUrl(uri, base); if (url) forgetSegment(url);
        }
        if (!line || line.startsWith('#')) continue;
        const url = resolveUrl(line, base);
        if (url && next === 'variant') { variants++; linkParent(url, base); }
        if (url && next === 'segment') forgetSegment(url);
        next = '';
      }
      if (subtitlePlaylists.has(base)) return;
      record(base, 'Verified playlist', 'application/vnd.apple.mpegurl', status, false,
        { ...context, contentIssue: '', confidence: 4, manifest: master ? 'master' : 'media', variants });
    } else if (/^\s*(?:<\?xml[^>]*>\s*)?<(?:[\w.-]+:)?MPD[\s>]/.test(text) && !/<!DOCTYPE|<!ENTITY/i.test(text)) {
      const xml = new DOMParser().parseFromString(text, 'application/xml');
      if (!xml.getElementsByTagName('parsererror').length) {
        inspectDashSegments(xml, base);
        const protection = [...xml.getElementsByTagNameNS('*', 'ContentProtection')];
        const declaredKids = protection.flatMap(element => [...element.attributes]
          .filter(a => a.localName === 'default_KID').flatMap(a => a.value.trim().split(/\s+/)));
        const parsedKids = declaredKids.map(kidFromUuid);
        const requiredKids = parsedKids.length <= 32 && parsedKids.every(Boolean) ? [...new Set(parsedKids)] : [];
        record(base, 'Verified manifest', 'application/dash+xml', status, false,
          { ...context, contentIssue: '', confidence: 4, manifest: 'dash', drm: protection.length > 0, requiredKids,
            clearKey: matchingClearKey(requiredKids, base) });
        scanConfiguredClearKeys(window.player);
      }
    } else if (/^\s*WEBVTT(?:\s|$)/.test(text) || /^\s*\d+\s*\r?\n\d{2}:\d{2}:\d{2}[,.]\d{3}\s*-->/.test(text) ||
      /^\s*\[Script Info\]/i.test(text) || /^\s*(?:<\?xml[^>]*>\s*)?<(?:[\w.-]+:)?tt[\s>]/.test(text) && !/<!DOCTYPE|<!ENTITY/i.test(text)) {
      if (/^\s*WEBVTT/.test(text) && /(?:#xywh=|\.(?:jpg|jpeg|png|webp)(?:[?#\s]|$))/i.test(text)) {
        nonSubtitleUrls.add(base); subtitleObservations.delete(base);
        for (const [source, tracks] of sourceSubtitles) if (tracks.some(t => t.url === base)) attachSubtitles(source, tracks.filter(t => t.url !== base), true);
        return;
      }
      const format = /^\s*WEBVTT/.test(text) ? 'vtt' : /^\s*\[Script Info\]/i.test(text) ? 'ass' : text.trimStart().startsWith('<') ? 'ttml' : 'srt';
      observeSubtitle(base, format, status, context, true);
    } else if (/^\s*[\[{]/.test(text)) {
      try { inspectObject(JSON.parse(text), base); } catch { /* not JSON */ }
      const item = items.get(base);
      if (item && ['HLS', 'DASH'].includes(item.kind)) publish({ ...item, contentIssue: 'manifest' });
    } else {
      const item = items.get(base);
      if (item && ['HLS', 'DASH'].includes(item.kind)) publish({ ...item,
        contentIssue: !text.trim() ? 'empty' : /^\s*(?:<!doctype html|<html)/i.test(text) ? 'html' : 'manifest' });
    }
  }

  function inspectable(mime, url) {
    return /mpegurl|dash\+xml|(?:application|text)\/(?:[^;]*\+)?json|text\/vtt|application\/(?:x-subrip|ttml\+xml)|(?:text|application)\/(?:x-)?(?:ass|ssa)/i.test(mime) ||
      /\.(m3u8|mpd|vtt|srt|ass|ssa|ttml)(?:[?#]|$)/i.test(url) || subtitleObservations.has(url) ||
      [...sourceSubtitles.values()].some(tracks => tracks.some(t => t.url === url));
  }

  function responseDestination(requested, destination) {
    const from = httpUrl(requested), to = httpUrl(destination);
    if (from && to) {
      const a = new URL(from), b = new URL(to); a.hash = ''; b.hash = '';
      if (a.href === b.href) return from; // fragments are not HTTP redirects
    }
    return to || from;
  }

  function observeRedirect(requested, destination, status) {
    const from = httpUrl(requested), to = responseDestination(requested, destination);
    if (!from || !to || from === to || status < 200 || status >= 300) return;
    if ((items.has(from) || redirectAliases.has(from)) && items.has(to)) {
      redirectAliases.set(from, to);
      if (redirectAliases.size > 150) redirectAliases.delete(redirectAliases.keys().next().value);
      const tracks = sourceSubtitles.get(from); if (tracks?.length) attachSubtitles(to, tracks);
      items.delete(from);
      if (!isTop) window.top.postMessage({ channel: CHANNEL, type: 'redirect', from, to }, '*');
    }
    // Caption redirects must replace their own URLs, not mix media headers into them.
    for (const [source, tracks] of sourceSubtitles) if (tracks.some(t => t.url === from)) {
      attachSubtitles(source, tracks.map(t => t.url === from ? { ...t, url: to } : t), true);
    }
  }

  function rememberBlob(blob, value, context) {
    const url = httpUrl(value);
    if (!url || !blob || blob.size > MAX_TEXT_BYTES) return;
    const info = { url, context }; blobSources.set(blob, info);
    for (const [objectUrl, entry] of blobUrls) if (entry.blob === blob) blobUrls.set(objectUrl, { ...info, blob });
    scanSubtitleTracks();
  }

  function rememberResponseBlob(response, url, context) {
    if (typeof response.blob !== 'function') return;
    const original = response.blob;
    try {
      response.blob = function (...args) {
        return original.apply(this, args).then(blob => { try { rememberBlob(blob, url, context); } catch {} return blob; });
      };
    } catch { /* response object may be non-writable */ }
  }

  if (typeof URL.createObjectURL === 'function') {
    const create = URL.createObjectURL, revoke = URL.revokeObjectURL;
    URL.createObjectURL = function (blob) {
      const url = create.apply(this, arguments);
      if (blob instanceof Blob && blob.size <= MAX_TEXT_BYTES) {
        blobUrls.set(url, { ...blobSources.get(blob), blob });
        if (blobUrls.size > 80) blobUrls.delete(blobUrls.keys().next().value);
      }
      return url;
    };
    URL.revokeObjectURL = function (url) {
      // Players often revoke a downloaded track after it has loaded. Keep the
      // bounded HTTP mapping while releasing the Blob reference; it remains
      // useful for the already-loaded track's later Cloudstream handoff.
      const info = blobUrls.get(url);
      if (info?.url) blobUrls.set(url, { url: info.url, context: info.context });
      return revoke.apply(this, arguments);
    };
  }

  function inspectResponse(response, requested, context) {
    const mime = response.headers.get('content-type') || '';
    const base = responseDestination(requested, response.url);
    if (!base || response.status < 200 || response.status >= 300 || pendingInspections >= 4 ||
        Number(response.headers.get('content-length')) > MAX_TEXT_BYTES ||
        !inspectable(mime, base)) return;
    let reader;
    try { reader = response.clone().body?.getReader(); } catch { return; }
    if (!reader) return;
    pendingInspections++;
    (async () => {
      let text = '', bytes = 0, cancelled = false;
      const decoder = new TextDecoder();
      const timeout = setTimeout(() => { cancelled = true; reader.cancel().catch(() => {}); }, 2000);
      try {
        for (;;) {
          const { value, done } = await reader.read();
          if (done) break;
          bytes += value.byteLength;
          if (bytes > MAX_TEXT_BYTES) { cancelled = true; reader.cancel().catch(() => {}); break; }
          text += decoder.decode(value, { stream: true });
        }
        if (!cancelled) inspectText(text + decoder.decode(), base, context, response.status);
      } catch { /* observation must not affect the original response */ }
      finally { clearTimeout(timeout); pendingInspections--; try { reader.releaseLock(); } catch {} }
    })();
  }

  function configuredHeaders(value) {
    // Do not consume a one-shot iterator passed as fetch headers: observation
    // must not change the request. Only read ordinary reusable containers.
    try {
      let rows = [];
      if (value instanceof Headers) rows = [...value.entries()];
      else if (Array.isArray(value)) rows = value;
      else if (value && [Object.prototype, null].includes(Object.getPrototypeOf(value))) rows = Object.entries(value);
      const result = Object.create(null);
      for (const entry of rows) {
        if (!Array.isArray(entry) || entry.length !== 2) continue;
        const name = String(entry[0]).toLowerCase(), text = String(entry[1]);
        // These non-secret headers are visible in request configuration.
        // Cookie, Authorization and arbitrary token headers stay manual.
        if (observableHeaders.has(name) && text.length <= 4096 && !/[\u0000-\u001f\u007f]/.test(text)) result[name] = text;
      }
      return result;
    } catch { return {}; }
  }

  function publish(item, fromFrame = false) {
    const url = httpUrl(item.url);
    const page = httpUrl(item.page);
    if (!url || !page || isSegment(url) || subtitlePlaylists.has(url) || !['HLS', 'DASH', 'MP4', 'WebM', 'Video', 'Video element', 'Audio'].includes(item.kind)) return;
    const old = items.get(url);
    const status = Number.isInteger(item.status) && item.status >= 0 && item.status <= 599 ? item.status : null;
    const confidence = [1, 2, 3, 4].includes(item.confidence) ? item.confidence : 1;
    const stronger = old && old.confidence > confidence;
    const headerContext = item.requestHeaders !== undefined;
    const requestHeaders = headerContext ? configuredHeaders(item.requestHeaders) : old?.requestHeaders || {};
    const browserAgent = typeof item.browserAgent === 'string' && item.browserAgent.length <= 1024 && !/[\u0000-\u001f\u007f]/.test(item.browserAgent) ? item.browserAgent : old?.browserAgent || navigator.userAgent;
    const requestMethod = typeof item.requestMethod === 'string' ? item.requestMethod.toUpperCase().slice(0, 16) : old?.requestMethod || 'GET';
    const suggestedReferer = stronger ? old.suggestedReferer : typeof item.suggestedReferer === 'string' && (item.suggestedReferer === '' || httpUrl(item.suggestedReferer)) ? item.suggestedReferer : old?.suggestedReferer ?? inferredReferer(url, page, documentPolicy());
    const validOrigin = typeof item.suggestedOrigin === 'string' && (['', 'null'].includes(item.suggestedOrigin) ||
      httpUrl(item.suggestedOrigin) && new URL(item.suggestedOrigin).origin === item.suggestedOrigin);
    const suggestedOrigin = stronger ? old.suggestedOrigin : validOrigin ? item.suggestedOrigin : old?.suggestedOrigin || '';
    const requiredKids = Array.isArray(item.requiredKids) ? [...new Set(item.requiredKids.filter(canonicalKey))].slice(0, 32) : old?.requiredKids || [];
    const key = item.clearKey;
    const clearKey = key && canonicalKey(key.kid) && canonicalKey(key.key) && requiredKids.length === 1 && key.kid === requiredKids[0]
      ? { kid: key.kid, key: key.key } : item.clearKey === null ? null : old?.clearKey || null;
    const title = typeof item.title === 'string' ? item.title.replace(/[\u0000-\u001f\u007f]/g, ' ').slice(0, 150) : old?.title || '';
    const subtitles = cleanSubtitles(item.subtitles === undefined ? old?.subtitles || [] : item.subtitles);
    const contentIssue = ['', 'html', 'empty', 'manifest'].includes(item.contentIssue) ? item.contentIssue : old?.contentIssue || '';
    const next = { subtitles, contentIssue, url, page: stronger ? old.page : page, kind: stronger ? old.kind : item.kind,
      confidence: stronger ? old.confidence : confidence, method: String(item.method).slice(0, 60),
      status: status ?? old?.status ?? null, requestHeaders, requestMethod, browserAgent, suggestedReferer, suggestedOrigin, title,
      active: typeof item.active === 'boolean' ? item.active : old?.active || false,
      manifest: ['master', 'media', 'dash'].includes(item.manifest) ? item.manifest : old?.manifest || '',
      variants: Number.isInteger(item.variants) ? Math.min(100, Math.max(0, item.variants)) : old?.variants || 0,
      requiredKids, clearKey, drm: typeof item.drm === 'boolean' ? item.drm : old?.drm || false, lastSeen: Date.now() };
    if (old && old.contentIssue === next.contentIssue && old.status === next.status && old.kind === next.kind && old.confidence === next.confidence && old.page === next.page &&
        old.requestMethod === next.requestMethod && JSON.stringify(old.requestHeaders) === JSON.stringify(next.requestHeaders) && old.browserAgent === next.browserAgent &&
        old.suggestedReferer === next.suggestedReferer && old.suggestedOrigin === next.suggestedOrigin && old.title === next.title && old.active === next.active &&
        old.manifest === next.manifest && old.variants === next.variants && old.drm === next.drm && JSON.stringify(old.subtitles) === JSON.stringify(next.subtitles) && JSON.stringify(old.requiredKids) === JSON.stringify(next.requiredKids) && JSON.stringify(old.clearKey) === JSON.stringify(next.clearKey) && next.lastSeen - old.lastSeen < 1000) return;
    if (!old && items.size >= LIMIT) {
      const first = [...items.values()].sort((a, b) => score(a) - score(b) || a.lastSeen - b.lastSeen)[0].url;
      items.delete(first); refererOverrides.delete(first); playbackOverrides.delete(first);
    }
    items.set(url, next);
    if (!isTop && !fromFrame) {
      window.top.postMessage({ channel: CHANNEL, type: 'media', item: next }, '*');
    }
    if (isTop) scheduleRender();
  }

  // Preserve the original response. Bounded clones of playlists/JSON improve
  // detection without reading binary media or issuing extra requests.
  if (typeof window.fetch === 'function') {
    const originalFetch = window.fetch;
    window.fetch = function (...args) {
      const requested = typeof args[0] === 'string' || args[0] instanceof URL ? args[0] : args[0]?.url;
      let context = {};
      try {
        const init = args[1], request = args[0] instanceof Request ? args[0] : null;
        context = { requestHeaders: configuredHeaders(init?.headers !== undefined ? init.headers : request?.headers),
          requestMethod: init?.method || request?.method || 'GET' };
        context.referrerSource = init?.referrer !== undefined ? init.referrer : request?.referrer ?? location.href;
        context.referrerPolicy = init?.referrerPolicy || request?.referrerPolicy || documentPolicy();
        context.requestMode = init?.mode || request?.mode || 'cors';
        context.suggestedReferer = inferredReferer(requested, context.referrerSource, context.referrerPolicy);
        context.suggestedOrigin = inferredOrigin(requested, context.requestMode, context.requestMethod);
        if (requested) record(requested, 'Fetch request', '', null, false, context);
      } catch { /* leave page behavior intact */ }
      return originalFetch.apply(this, args).then(response => {
        try {
          const mime = response.headers.get('content-type') || '';
          if (requested) record(requested, 'Fetch response', mime, response.status, false, context);
          // Do not copy configured headers to a different redirect origin:
          // the browser may have stripped them during that redirect.
          const sameOrigin = response.url && httpUrl(requested) && new URL(response.url).origin === new URL(httpUrl(requested)).origin;
          const destinationContext = { ...context, requestHeaders: sameOrigin ? context.requestHeaders : {},
            suggestedReferer: inferredReferer(response.url || requested, context.referrerSource, context.referrerPolicy),
            suggestedOrigin: inferredOrigin(response.url || requested, context.requestMode, context.requestMethod) };
          if (response.url) record(responseDestination(requested, response.url), 'Fetch response / destination', mime, response.status, false, destinationContext);
          observeRedirect(requested, response.url, response.status);
          rememberResponseBlob(response, response.url || requested, destinationContext);
          observeSubtitle(response.url || requested, mime, response.status, destinationContext);
          inspectResponse(response, requested, destinationContext);
        } catch { /* observation must not break the original response */ }
        return response;
      }, error => {
        try { if (requested) record(requested, 'Fetch failed', '', 0, false, context); } catch { /* observe only */ }
        throw error;
      });
    };
  }

  if (typeof window.XMLHttpRequest === 'function') {
    const urls = new WeakMap();
    const proto = window.XMLHttpRequest.prototype;
    const originalOpen = proto.open;
    const originalSend = proto.send;
    const originalSetHeader = proto.setRequestHeader;
    proto.open = function (...args) {
      const result = originalOpen.apply(this, args);
      const state = { url: args[1], requestMethod: String(args[0]).toUpperCase(), requestHeaders: {},
        referrerPolicy: documentPolicy(),
        suggestedReferer: inferredReferer(args[1], location.href, documentPolicy()),
        suggestedOrigin: inferredOrigin(args[1], 'cors', args[0]) };
      urls.set(this, state);
      try { record(args[1], 'XHR request', '', null, false, state); } catch { /* observe only */ }
      return result;
    };
    proto.setRequestHeader = function (name, value) {
      const result = originalSetHeader.apply(this, arguments);
      try {
        const state = urls.get(this), lower = String(name).toLowerCase();
        if (state && observableHeaders.has(lower)) {
          // XHR combines repeated headers with comma+space.
          state.requestHeaders[lower] = state.requestHeaders[lower] === undefined ? String(value) : state.requestHeaders[lower] + ', ' + String(value);
        }
      } catch { /* observe only */ }
      return result;
    };
    proto.send = function (...args) {
      try {
        const state = urls.get(this);
        if (state) record(state.url, 'XHR request', '', null, false, state);
      } catch { /* observe only */ }
      this.addEventListener('loadend', () => {
        try {
          const mime = this.getResponseHeader('content-type') || '';
          const state = urls.get(this);
          if (state) record(state.url, 'XHR response', mime, this.status, false, state);
          const sameOrigin = state && httpUrl(state.url) && this.responseURL && new URL(this.responseURL).origin === new URL(httpUrl(state.url)).origin;
          const destinationContext = { ...(state || {}), requestHeaders: sameOrigin ? state.requestHeaders : {},
            suggestedReferer: inferredReferer(this.responseURL || state?.url, location.href, state?.referrerPolicy || documentPolicy()),
            suggestedOrigin: inferredOrigin(this.responseURL || state?.url, 'cors', state?.requestMethod || 'GET') };
          if (this.responseURL) record(responseDestination(state?.url, this.responseURL), 'XHR response / destination', mime, this.status, false, destinationContext);
          observeRedirect(state?.url, this.responseURL, this.status);
          if (this.responseType === 'blob' && this.response instanceof Blob) rememberBlob(this.response, this.responseURL || state?.url, destinationContext);
          observeSubtitle(this.responseURL || state?.url, mime, this.status, destinationContext);
          if (this.status >= 200 && this.status < 300 && inspectable(mime, this.responseURL || state?.url || '')) {
            if (this.responseType === 'json') inspectObject(this.response, this.responseURL || httpUrl(state?.url));
            else if ((!this.responseType || this.responseType === 'text') && this.responseText.length <= MAX_TEXT_BYTES) {
              inspectText(this.responseText, this.responseURL || httpUrl(state?.url), destinationContext, this.status);
            } else if (this.responseType === 'arraybuffer' && this.response?.byteLength <= MAX_TEXT_BYTES) {
              inspectText(new TextDecoder('utf-8', { fatal: true }).decode(this.response),
                this.responseURL || httpUrl(state?.url), destinationContext, this.status);
            } else if (this.responseType === 'blob' && this.response?.size <= MAX_TEXT_BYTES) {
              const base = this.responseURL || httpUrl(state?.url), status = this.status;
              this.response.text().then(text => inspectText(text, base, destinationContext, status)).catch(() => {});
            }
          }
        } catch { /* observe only */ }
      }, { once: true });
      return originalSend.apply(this, args);
    };
  }

  function resources(entries) {
    for (const entry of entries) record(entry.name, `Resource: ${entry.initiatorType || 'network'}`);
  }
  try {
    resources(performance.getEntriesByType('resource'));
    new PerformanceObserver(list => resources(list.getEntries())).observe({ type: 'resource', buffered: true });
  } catch { /* not supported in every browser */ }

  function scanVideos() {
    const candidates = new Map(), activeUrls = new Set();
    for (const element of queryMediaRoots('video, video source, audio, audio source')) {
      const src = element.currentSrc || element.src || element.getAttribute('src');
      const url = src && httpUrl(src), player = element.matches('source') ? element.parentElement : element;
      if (!url) continue;
      const active = !!player?.isConnected && !player.paused && !player.ended && httpUrl(player.currentSrc || player.src) === url;
      if (active) activeUrls.add(url);
      const old = candidates.get(url);
      candidates.set(url, { element, active: active || old?.active || false, title: player?.getAttribute('title') || document.title });
    }
    for (const [url, candidate] of candidates) record(url, 'Video element', candidate.element.type || '', null, true,
      { active: candidate.active, title: candidate.title, suggestedReferer: inferredReferer(url, location.href, documentPolicy()) });
    scanPlayerTracks(); scanSubtitleTracks();
    for (const item of items.values()) if (item.page === location.href && item.active && !activeUrls.has(item.url)) {
      publish({ ...item, active: false });
    }
  }

  function scanPageSources() {
    for (const script of queryMediaRoots('script[type="application/ld+json"], script[type="application/json"]')) {
      if (script.textContent.length <= MAX_TEXT_BYTES) {
        try { inspectObject(JSON.parse(script.textContent), location.href); } catch { /* not JSON */ }
      }
    }
    for (const element of queryMediaRoots('link[rel="preload"][as="video"], link[rel="preload"][as="audio"], meta[property="og:video"], meta[property="og:video:url"], meta[property="og:video:secure_url"]')) {
      const url = element.getAttribute('href') || element.getAttribute('content');
      if (url) record(url, 'Available page source', element.type || '');
    }
  }

  function queryMediaRoots(selector) {
    return [...mediaRoots].flatMap(root => [...root.querySelectorAll(selector)]);
  }

  function watchMediaRoot(root) {
    if (mediaRoots.has(root) || mediaRoots.size >= 32 || root.host?.id === 'cloudstream-media-finder') return;
    mediaRoots.add(root);
    new MutationObserver(onMutations).observe(root, { subtree: true, childList: true, attributes: true, attributeFilter: ['src', 'type', 'content', 'label', 'srclang', 'kind'] });
    for (const event of ['play', 'playing', 'pause', 'ended', 'loadedmetadata', 'emptied']) {
      root.addEventListener(event, e => { if (e.target.matches?.('video, audio')) scanVideos(); }, true);
    }
  }

  function discoverShadowRoots(node) {
    const elements = [node, ...node.querySelectorAll?.('*') || []].slice(0, 4000);
    for (const element of elements) if (element.shadowRoot) {
      watchMediaRoot(element.shadowRoot);
      if (mediaRoots.size < 32) discoverShadowRoots(element.shadowRoot);
    }
  }

  if (Element.prototype.attachShadow) {
    const attachShadow = Element.prototype.attachShadow;
    Element.prototype.attachShadow = function (...args) {
      const root = attachShadow.apply(this, args);
      try { if (root.mode === 'open') watchMediaRoot(root); } catch { /* preserve page behavior */ }
      return root;
    };
  }
  watchMediaRoot(document);

  function askFrames() {
    for (const frame of document.querySelectorAll('iframe, frame')) {
      try { frame.contentWindow?.postMessage({ channel: CHANNEL, type: 'report' }, '*'); } catch { /* inaccessible */ }
    }
  }

  window.addEventListener('message', event => {
    const message = event.data;
    if (!message || message.channel !== CHANNEL || !event.source) return;
    if (isTop && event.source !== window && message.type === 'media' && message.item) {
      publish(message.item, true);
    } else if (isTop && event.source !== window && message.type === 'redirect' && httpUrl(message.from) && httpUrl(message.to)) {
      observeRedirect(message.from, message.to, 200);
    } else if (isTop && event.source !== window && message.type === 'subtitlePlaylist' && httpUrl(message.url)) {
      markSubtitlePlaylist(httpUrl(message.url));
    } else if (isTop && event.source !== window && message.type === 'dashRule') {
      addDashRule(message.template, true);
    } else if (isTop && event.source !== window && message.type === 'segment' && httpUrl(message.url)) {
      forgetSegment(httpUrl(message.url));
    } else if (isTop && event.source !== window && message.type === 'parent' && httpUrl(message.url) && httpUrl(message.parent)) {
      linkParent(httpUrl(message.url), httpUrl(message.parent));
    } else if (!isTop && message.type === 'report' && (event.source === window.parent || event.source === window.top)) {
      for (const url of subtitlePlaylists) window.top.postMessage({ channel: CHANNEL, type: 'subtitlePlaylist', url }, '*');
      for (const template of dashRules.keys()) window.top.postMessage({ channel: CHANNEL, type: 'dashRule', template }, '*');
      for (const item of items.values()) window.top.postMessage({ channel: CHANNEL, type: 'media', item }, '*');
      scanVideos();
      scanPageSources();
      askFrames();
    }
  });

  function scheduleRender() {
    if (!ui || renderPending) return;
    renderPending = true;
    setTimeout(() => { renderPending = false; render(); }, 100);
  }

  function node(tag, text, parent, className) {
    const element = document.createElement(tag);
    if (text !== undefined) element.textContent = text;
    if (className) element.className = className;
    if (parent) parent.appendChild(element);
    return element;
  }

  async function copy(value, button, input, label) {
    try {
      await navigator.clipboard.writeText(value);
      button.textContent = 'Copied';
    } catch {
      const details = input.closest('details'); if (details) details.open = true;
      input.focus(); input.select();
      try { button.textContent = document.execCommand('copy') ? 'Copied' : 'Select and copy'; }
      catch { button.textContent = 'Select and copy'; }
    }
    setTimeout(() => { button.textContent = label; }, 1800);
  }

  function settingsFor(item) {
    if (!playbackOverrides.has(item.url)) playbackOverrides.set(item.url, {
      ua: item.browserAgent || navigator.userAgent, origin: null, headersText: null, type: '', expanded: false, includeSubtitles: true
    });
    return playbackOverrides.get(item.url);
  }

  function validateHeaders(text) {
    const result = Object.create(null), seen = new Set();
    if (!text.trim()) return result;
    if (text.length > 16384) throw new Error('Custom headers are too long.');
    let parsed;
    try { parsed = JSON.parse(text); } catch { throw new Error('Custom headers must be a JSON object, such as {"Accept":"*/*"}.'); }
    if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed) || Object.keys(parsed).length > 20) throw new Error('Use a JSON object with at most 20 headers.');
    let total = 0;
    for (const [name, value] of Object.entries(parsed)) {
      const lower = name.toLowerCase();
      if (!/^[!#$%&'*+.^_`|~0-9A-Za-z-]{1,64}$/.test(name) || reservedHeaders.has(lower) || /^(proxy-|sec-|access-control-request-)/.test(lower)) throw new Error('Unsupported header: ' + name + '. Use the dedicated Referer, User-Agent or Origin fields; playback manages transport headers.');
      if (seen.has(lower)) throw new Error('Duplicate header: ' + name);
      seen.add(lower);
      if (typeof value !== 'string' || value.length > 4096 || /[\u0000-\u001f\u007f]/.test(value)) throw new Error('Header values must be strings without line breaks/control characters.');
      total += name.length + value.length;
      if (total > 8192) throw new Error('Custom headers are too long.');
      result[name] = value;
    }
    return result;
  }

  function appLinks(item, referer) {
    let ref = referer.trim();
    if (ref) {
      if (!/^https?:\/\//i.test(ref)) throw new Error('Referer must be an HTTP(S) URL, or empty.');
      ref = httpUrl(ref);
      if (!ref) throw new Error('Referer must be an HTTP(S) URL without embedded credentials.');
    }
    const title = (document.title || 'Browser stream').replace(/[\u0000-\u001f\u007f]/g, ' ').slice(0, 300);
    const settings = settingsFor(item), ua = settings.ua.trim();
    if (/[\u0000-\u001f\u007f]/.test(ua)) throw new Error('User-Agent cannot contain line breaks or control characters.');
    let origin = (settings.origin ?? item.suggestedOrigin ?? '').trim();
    if (origin && origin !== 'null') {
      const parsed = httpUrl(origin);
      if (!/^https?:\/\//i.test(origin) || !parsed) throw new Error('Origin must be an HTTP(S) origin, null, or empty.');
      const value = new URL(parsed);
      if (!['', '/'].includes(value.pathname) || value.search || value.hash) throw new Error('Origin contains only scheme, host and optional port; remove the page path.');
      origin = value.origin;
    }
    const headers = validateHeaders(settings.headersText ?? JSON.stringify(item.requestHeaders || {}));
    const headersJson = JSON.stringify(headers);
    if (headersJson.length > 16384) throw new Error('Custom headers are too long.');
    if (item.url.length > 16384 || ref.length > 8192 || ua.length > 1024 || origin.length > 8192) throw new Error('This link is too long for the bridge. Use Copy link for manual playback.');
    const type = settings.type || (item.kind === 'HLS' ? 'hls' : item.kind === 'DASH' ? 'dash' : item.kind === 'Video element' ? 'auto' : 'video');
    const fields = { v: '2', url: item.url, referer: ref, type, name: title, ua, origin, headers: headersJson };
    if (type === 'dash' && item.clearKey) { fields.v = '3'; fields.clearkey = JSON.stringify(item.clearKey); }
    const subtitles = settings.includeSubtitles === false ? [] : cleanSubtitles(item.subtitles);
    const subtitleCount = subtitles.length, baseVersion = fields.v;
    for (;;) {
      if (subtitles.length && JSON.stringify(subtitles).length <= 24576) {
        fields.v = subtitles.some(s => Object.keys(s.headers || {}).length) ? '5' : '4'; fields.subtitles = JSON.stringify(subtitles);
      } else {
        delete fields.subtitles; fields.v = baseVersion;
        if (subtitles.length) { subtitles.pop(); continue; }
      }
      const carrier = 'https://browser-stream.cloudstream.invalid/play?' + new URLSearchParams(fields).toString();
      // Android Uri.authority decodes once, then Cloudstream's player handler
      // uses URLDecoder once more. Both layers are intentional: signed URLs
      // must retain literal +, %2F, &, = and all existing query parameters.
      // Cloudstream checks for its OAuth scheme substring before its player
      // scheme. Fully escape the outer authority/title so a token or title
      // containing "cloudstreamapp" cannot take that unrelated branch.
      const escapeAll = value => encodeURIComponent(value).replace(/%[0-9A-F]{2}|[A-Za-z0-9_.!~*'()-]/g, part =>
        part.startsWith('%') ? part : '%' + part.charCodeAt(0).toString(16).toUpperCase().padStart(2, '0'));
      const deepLink = 'cloudstreamplayer://' + escapeAll(encodeURIComponent(carrier)) + '?name=' + escapeAll(title);
      // The official redirect page also decodes twice: URLSearchParams.get,
      // followed by decodeURIComponent. This route already works on the phone.
      const redirect = 'https://recloudstream.github.io/csredirect?redirectto=' + encodeURIComponent(encodeURIComponent(deepLink));
      if (carrier.length <= 65536 && deepLink.length <= 262144) return { direct: deepLink, redirect, omittedSubtitles: subtitleCount - subtitles.length };
      if (subtitles.length) { subtitles.pop(); continue; }
      throw new Error('This link is too long for the bridge. Use Copy link for manual playback.');
    }
  }

  function mount() {
    if (!isTop || ui || !document.documentElement) return;
    const host = document.createElement('div');
    host.id = 'cloudstream-media-finder';
    host.style.cssText = 'position:fixed;right:12px;bottom:12px;z-index:2147483647;display:flex;flex-direction:column;align-items:flex-end;';
    const shadow = host.attachShadow({ mode: 'open' });
    node('style', `
      :host{all:initial;color-scheme:dark;font:14px system-ui,sans-serif;color:#eee}
      *{box-sizing:border-box}button,a[role=button]{border:1px solid #53637b;border-radius:7px;background:#26364e;color:#fff;padding:9px 12px;cursor:pointer;font:inherit;text-decoration:none}
      .panel{background:#111820;border:1px solid #46556a;border-radius:12px;width:min(560px,calc(100vw - 24px));max-height:72vh;overflow:auto;box-shadow:0 8px 40px #0009;margin-bottom:8px;padding:14px}
      .panel[hidden]{display:none}h2{font-size:18px;margin:0 0 8px}p{line-height:1.45;color:#bcc8d8;margin:8px 0}.toolbar{display:flex;gap:8px;flex-wrap:wrap;margin:10px 0}
      h3{font-size:15px;line-height:1.4;margin:0 0 7px;overflow-wrap:anywhere}.tags{display:flex;flex-wrap:wrap;gap:6px}.tag{font-size:11px;color:#bac9dc;background:#202b3b;padding:3px 7px;border-radius:5px}.tag.active{color:#b5f2d2;background:#16422e}.secondary{background:#202b3b}.actions>a.open[role=button]{font-weight:600;background:#19563b;border-color:#34825d;min-width:170px;flex:1.4}.actions>.secondary{flex:1;min-width:104px}.actions>.open,.actions>.secondary{text-align:center}
      .item{border-top:1px solid #354154;padding:12px 0}.meta{font-size:12px;color:#bdc9da;margin:4px 0;overflow-wrap:anywhere}
      .row{display:flex;gap:8px}.row button{white-space:nowrap}input,textarea,select{width:100%;min-width:0;background:#080d14;color:#eee;border:1px solid #46556a;border-radius:6px;padding:8px;font:12px monospace}input[type=checkbox]{width:auto;vertical-align:middle;padding:0}textarea{min-height:90px;resize:vertical}summary{cursor:pointer;color:#bcc8d8;margin:10px 0}details .toolbar{margin:6px 0 12px}label{display:block;margin:8px 0 4px;color:#bcc8d8;font-size:12px}
      strong{color:#f2f7ff}.empty{padding:14px 0}.warning{color:#ffcd8d}.actions{display:flex;gap:8px;flex-wrap:wrap;margin-top:10px}.open{background:#19563b}
    `, shadow);
    const panel = node('section', undefined, shadow, 'panel');
    panel.hidden = true;
    node('h2', 'Play in Cloudstream', panel);
    node('p', 'Start a video on this page, then choose a source below.', panel);
    const toolbar = node('div', undefined, panel, 'toolbar');
    const rescan = node('button', 'Rescan', toolbar);
    rescan.onclick = () => { discoverShadowRoots(document); scanVideos(); scanPageSources(); resources(performance.getEntriesByType('resource')); askFrames(); render(); };
    const clear = node('button', 'Clear', toolbar);
    clear.onclick = () => { items.clear(); clearKeys.clear(); playerClearKeys.clear(); sourceSubtitles.clear(); subtitleObservations.clear(); configuredCaptionSources.clear(); nonSubtitleUrls.clear(); refererOverrides.clear(); playbackOverrides.clear(); render(); };
    const hide = node('button', 'Close', toolbar);
    hide.onclick = () => { panel.hidden = true; };
    const more = node('button', 'Show all sources', toolbar);
    more.hidden = true;
    more.onclick = () => { showAll = !showAll; render(); };
    const list = node('div', undefined, panel);
    const toggle = node('button', 'Media: 0', shadow);
    toggle.onclick = () => { panel.hidden = !panel.hidden; if (!panel.hidden) { scanVideos(); askFrames(); render(); } };
    document.documentElement.appendChild(host);
    ui = { panel, list, toggle, shadow, more };
    render();
  }

  function render() {
    if (!ui) return;
    ui.toggle.textContent = `Media: ${items.size}`;
    // New observations must not remove an input while the user edits/copies it.
    // The pending changes are rendered on blur instead.
    if (['INPUT', 'TEXTAREA', 'SELECT'].includes(ui.shadow.activeElement?.tagName)) return;
    if (!items.size) {
      ui.list.replaceChildren(); cards.clear(); ui.more.hidden = true;
      node('p', 'No media found yet. Start playback or reload with the userscript enabled. Scripts must also run inside embedded-player frames.', ui.list, 'empty');
      return;
    }
    ui.list.querySelector('.empty')?.remove();
    for (const [url, entry] of cards) {
      if (!items.has(url)) { entry.card.remove(); cards.delete(url); }
    }
    const sorted = [...items.values()].sort((a, b) => score(b) - score(a) || b.lastSeen - a.lastSeen);
    const preferred = sorted.filter(item => {
      if (redirectAliases.has(item.url) && items.has(redirectAliases.get(item.url))) return false;
      const parent = items.get(playlistParents.get(item.url));
      return !parent || parent.manifest !== 'master' || parent.status >= 400;
    }).slice(0, 8);
    const displayed = showAll ? sorted : preferred;
    ui.more.hidden = displayed.length === sorted.length && !showAll;
    ui.more.textContent = showAll ? 'Show suggested sources' : `Show all sources (${sorted.length})`;
    const visibleUrls = new Set(displayed.map(item => item.url));
    for (const [url, entry] of cards) if (!visibleUrls.has(url)) { entry.card.remove(); cards.delete(url); }
    let index = 0;
    for (const item of displayed) {
      const signature = JSON.stringify([item.kind, item.method, item.status, item.page, item.requestMethod, item.requestHeaders,
        item.active, item.contentIssue, item.manifest, item.variants, item.drm, item.clearKey, item.subtitles, item.title, item.suggestedReferer, item.suggestedOrigin, index]);
      const existing = cards.get(item.url);
      if (existing?.signature === signature) {
        // Keep buttons, edited fields, feedback and manual-copy fallbacks
        // alive when other media requests arrive or an input loses focus.
        if (ui.list.children[index] !== existing.card) ui.list.insertBefore(existing.card, ui.list.children[index] || null);
        index++;
        continue;
      }
      existing?.card.remove();
      const card = node('div', undefined, ui.list, 'item');
      card.dataset.mediaUrl = item.url;
      if (ui.list.children[index] !== card) ui.list.insertBefore(card, ui.list.children[index] || null);
      index++;
      node('h3', item.title || document.title || 'Media source', card);
      const tags = node('div', undefined, card, 'tags');
      node('span', `Source ${index}`, tags, 'tag');
      node('span', item.manifest === 'master' ? 'Adaptive video' : item.kind === 'Audio' ? 'Audio' : item.kind === 'HLS' || item.kind === 'DASH' ? 'Video stream' : 'Video', tags, 'tag');
      if (item.active) node('span', 'Playing in browser', tags, 'tag active');
      else if (index === 1 && score(item) > 0) node('span', 'Suggested', tags, 'tag active');
      if (item.variants) node('span', `${item.variants} quality options`, tags, 'tag');
      const actions = node('div', undefined, card, 'actions');
      const open = node('a', 'Play in Cloudstream', actions, 'open');
      open.setAttribute('role', 'button'); open.href = '#'; open.target = '_self';
      const copyRedirect = node('button', 'Copy redirect link', actions, 'secondary');
      const message = node('div', '', card, 'meta warning');
      message.setAttribute('aria-live', 'polite');
      if (item.contentIssue) node('div', item.contentIssue === 'html' ? 'The browser received a webpage instead of media. Start the player again or choose another source.' : 'The browser received an empty or invalid manifest. Start the player again or choose another source.', card, 'meta warning');
      else if (item.drm && !item.clearKey) node('div', 'This source uses content protection; a link alone may not play it.', card, 'meta warning');
      else if (item.status >= 400) node('div', 'The browser reported a problem with this source. Try another one.', card, 'meta warning');
      const settings = settingsFor(item);
      const advanced = node('details', undefined, card);
      advanced.open = settings.expanded;
      advanced.ontoggle = () => { settings.expanded = advanced.open; };
      node('summary', 'Options', advanced);
      node('strong', `${item.kind} · ${new URL(item.url).host}`, advanced);
      const status = item.status === null ? 'status not observed' : item.status === 0 ? 'response unavailable' : `HTTP ${item.status}`;
      node('div', `${item.method} · ${status}`, advanced, 'meta');
      node('div', `Page/player: ${item.page}`, advanced, 'meta');
      if (item.drm) node('div', item.clearKey ? 'ClearKey playback settings: matched to this manifest' :
        `Content protection detected; ${item.requiredKids.length} key identifier(s), no matching ClearKey settings captured.`, advanced, 'meta');
      if (item.status >= 400) node('div', 'This request failed; the URL may not play.', advanced, 'meta warning');
      else if (item.status === 0) node('div', 'The response status is unavailable; playback has not been verified.', advanced, 'meta warning');
      if (item.requestMethod !== 'GET') node('div', `Requested with ${item.requestMethod}; Cloudstream normally plays with GET. This URL may need a different stream request.`, advanced, 'meta warning');
      node('label', 'Media URL', advanced);
      const row = node('div', undefined, advanced, 'row');
      const input = node('input', undefined, row);
      input.type = 'text'; input.readOnly = true; input.value = item.url;
      input.setAttribute('aria-label', 'Media URL');
      const button = node('button', 'Copy media URL', row);
      button.onclick = () => copy(item.url, button, input, 'Copy media URL');
      node('div', 'Suggested Referer · page/player and visible referrer policy; the actual header may differ', advanced, 'meta');
      const refRow = node('div', undefined, advanced, 'row');
      const refInput = node('input', undefined, refRow);
      refInput.type = 'text'; refInput.value = refererOverrides.has(item.url) ? refererOverrides.get(item.url) : item.suggestedReferer;
      refInput.setAttribute('aria-label', 'Suggested Referer');
      refInput.placeholder = 'Leave empty to send no Referer';
      refInput.oninput = () => refererOverrides.set(item.url, refInput.value);
      refInput.onblur = scheduleRender;
      input.onblur = scheduleRender;
      const refButton = node('button', 'Copy Referer', refRow);
      refButton.onclick = () => copy(refInput.value, refButton, refInput, 'Copy Referer');
      node('label', 'User-Agent · empty uses Cloudstream’s default', advanced);
      const uaInput = node('input', undefined, advanced);
      uaInput.value = settings.ua; uaInput.setAttribute('aria-label', 'User-Agent');
      uaInput.oninput = () => { settings.ua = uaInput.value; }; uaInput.onblur = scheduleRender;
      const uaButtons = node('div', undefined, advanced, 'toolbar');
      node('button', 'Use browser UA', uaButtons).onclick = () => { settings.ua = item.browserAgent || navigator.userAgent; uaInput.value = settings.ua; };
      node('button', 'Use Cloudstream default', uaButtons).onclick = () => { settings.ua = ''; uaInput.value = ''; };
      node('label', 'Origin · inferred for cross-origin CORS requests; still editable', advanced);
      const originInput = node('input', undefined, advanced);
      originInput.value = settings.origin ?? item.suggestedOrigin ?? ''; originInput.placeholder = 'https://player.example'; originInput.setAttribute('aria-label', 'Origin');
      originInput.oninput = () => { settings.origin = originInput.value; }; originInput.onblur = scheduleRender;
      const originButtons = node('div', undefined, advanced, 'toolbar');
      node('button', 'Use inferred Origin', originButtons).onclick = () => { settings.origin = null; originInput.value = (items.get(item.url) || item).suggestedOrigin || ''; };
      node('button', 'Use player origin', originButtons).onclick = () => { settings.origin = new URL(item.page).origin; originInput.value = settings.origin; };
      node('button', 'No Origin', originButtons).onclick = () => { settings.origin = ''; originInput.value = ''; };
      node('label', 'Custom headers · JSON object', advanced);
      const headersInput = node('textarea', undefined, advanced);
      headersInput.value = settings.headersText ?? JSON.stringify(item.requestHeaders || {}, null, 2);
      headersInput.setAttribute('aria-label', 'Custom headers');
      headersInput.oninput = () => { settings.headersText = headersInput.value; }; headersInput.onblur = scheduleRender;
      const headerButtons = node('div', undefined, advanced, 'toolbar');
      node('button', 'Use observed headers', headerButtons).onclick = () => { settings.headersText = null; headersInput.value = JSON.stringify(item.requestHeaders || {}, null, 2); };
      node('button', 'No custom headers', headerButtons).onclick = () => { settings.headersText = '{}'; headersInput.value = '{}'; };
      node('p', 'Only page-configured Accept, Accept-Language and X-Requested-With are copied automatically. Add Cookie, Authorization or other required headers here if you know their values; browser-managed and HttpOnly cookies cannot be read by this script.', advanced);
      node('label', 'Stream type', advanced);
      const typeInput = node('select', undefined, advanced);
      for (const [value, label] of [['', 'Detected type'], ['hls', 'HLS (.m3u8)'], ['dash', 'DASH (.mpd)'], ['video', 'Direct video']]) {
        const option = node('option', label, typeInput); option.value = value;
      }
      typeInput.value = settings.type; typeInput.setAttribute('aria-label', 'Stream type');
      typeInput.onchange = () => { settings.type = typeInput.value; }; typeInput.onblur = scheduleRender;
      const fallbackActions = node('div', undefined, advanced, 'actions');
      const copyApp = node('button', 'Copy app link', fallbackActions);
      const copyDiagnostics = node('button', 'Copy diagnostics', fallbackActions);
      const redirectOpen = node('a', 'Open via HTTPS redirect', fallbackActions);
      redirectOpen.setAttribute('role', 'button'); redirectOpen.href = '#'; redirectOpen.target = '_self';
      redirectOpen.rel = 'noreferrer';
      const captionsLabel = node('label', undefined, advanced);
      const captionsInput = node('input', undefined, captionsLabel);
      captionsInput.type = 'checkbox'; captionsInput.checked = settings.includeSubtitles !== false;
      captionsInput.setAttribute('aria-label', 'Include detected subtitles');
      captionsInput.onchange = () => { settings.includeSubtitles = captionsInput.checked; };
      captionsLabel.append(document.createTextNode(' Include detected subtitles'));
      node('div', item.subtitles?.length ? `${item.subtitles.length} subtitle track(s): ${item.subtitles.map(s => s.name).join(', ')}` :
        'No external subtitles found yet. Enable the desired subtitle in the website player, then Rescan.', advanced, 'meta');
      node('p', 'Choose the subtitle language in Cloudstream’s player. HLS/DASH text renditions stay inside their original master manifest. Browser-only generated captions without an HTTP source cannot be transferred.', advanced);
      node('p', 'The main button opens the app directly in this tab. If your browser blocks it, try the HTTPS redirect. That fallback replaces this tab; use Back to return. Custom headers are excluded from redirect links.', advanced);
      function makeLink() {
        try { const links = appLinks(items.get(item.url) || item, refInput.value); message.textContent = links.omittedSubtitles ? `${links.omittedSubtitles} subtitle track(s) omitted to fit the app link; video is included.` : ''; return links; }
        catch (error) { message.textContent = error.message; return null; }
      }
      open.onclick = event => {
        const links = makeLink();
        if (!links) { event.preventDefault(); return; }
        // Use the anchor's native default action under the user gesture,
        // with _self and no window.open or invisible popup/iframe.
        open.href = links.direct;
        message.textContent = 'Opening Cloudstream… If it does not open, try the fallback under Options.' + (links.omittedSubtitles ? ` ${links.omittedSubtitles} subtitle track(s) did not fit the app link.` : '');
      };
      function copyLink(link, button, label) {
        const fallback = node('input', undefined, advanced);
        fallback.type = 'text'; fallback.readOnly = true; fallback.value = link;
        fallback.setAttribute('aria-label', label === 'Copy diagnostics' ? 'Playback diagnostics' : 'Cloudstream app link'); fallback.onblur = scheduleRender;
        copy(link, button, fallback, label).then(() => {
          if (button.textContent === 'Copied') fallback.remove();
        });
      }
      copyApp.onclick = () => {
        const links = makeLink();
        if (links) copyLink(links.direct, copyApp, 'Copy app link');
      };
      copyDiagnostics.onclick = () => {
        const current = items.get(item.url) || item;
        const state = settingsFor(current);
        const report = {
          finderVersion: FINDER_VERSION, expectedBridgeVersion: 7,
          kind: current.kind, manifest: current.manifest || 'not verified',
          httpStatus: current.status, contentIssue: current.contentIssue || 'none', requestMethod: current.requestMethod,
          sourceOrigin: new URL(current.url).origin,
          playerOrigin: new URL(current.page).origin,
          protected: current.drm, requiredKeyCount: current.requiredKids.length,
          matchingClearKey: !!current.clearKey, subtitleCount: current.subtitles.length, subtitleFormats: current.subtitles.map(s => s.format || 'unknown'),
          subtitleHeaderNames: [...new Set(current.subtitles.flatMap(s => Object.keys(s.headers || {})))],
          streamTypeOverride: state.type || 'none',
          emeObservers: current.page !== location.href ? 'player frame' :
            !emeHooks.length ? 'unavailable' : emeHooks.every(([proto, name, hook]) => proto[name] === hook) ? 'installed' : 'replaced by page',
          userAgentProvided: !!state.ua, originProvided: !!(state.origin ?? current.suggestedOrigin),
          customHeaderNames: [], directLinkLength: null
        };
        try {
          report.customHeaderNames = Object.keys(validateHeaders(state.headersText ?? JSON.stringify(current.requestHeaders || {})));
          report.directLinkLength = appLinks(current, refInput.value).direct.length;
        } catch { report.settingsValid = false; }
        // No media paths/queries, Referer values, keys, header values, or app
        // links are included. Safe to share when the app reports no source.
        copyLink(JSON.stringify(report, null, 2), copyDiagnostics, 'Copy diagnostics');
      };
      function redirectLink() {
        if ((items.get(item.url) || item).clearKey) {
          message.textContent = 'Use the direct app button for this source. HTTPS fallback does not share playback keys.';
          return null;
        }
        const links = makeLink();
        if (!links) return null;
        // Any extra header might contain private tokens. Redirecting them
        // through a third-party query string is neither necessary nor safe.
        const state = settingsFor(items.get(item.url) || item);
        const headers = validateHeaders(state.headersText ?? JSON.stringify((items.get(item.url) || item).requestHeaders || {}));
        if (Object.keys(headers).length || state.includeSubtitles !== false && (items.get(item.url) || item).subtitles.some(s => Object.keys(s.headers || {}).length)) {
          message.textContent = 'HTTPS fallback is disabled while custom headers are set. Use the direct app button, or choose No custom headers first.';
          return null;
        }
        if (links.redirect.length > 262144) { message.textContent = 'The HTTPS fallback link is too long. Use the direct app button.'; return null; }
        return links.redirect;
      }
      redirectOpen.onclick = event => {
        const link = redirectLink();
        if (!link) { event.preventDefault(); return; }
        redirectOpen.href = link;
      };
      copyRedirect.onclick = () => {
        const link = redirectLink();
        if (link) copyLink(link, copyRedirect, 'Copy redirect link');
      };
      cards.set(item.url, { card, signature });
    }
  }

  let playerPoll;
  function startPlayerPoll() {
    if (playerPoll) return;
    playerPoll = setInterval(() => { if (!document.hidden && queryMediaRoots('video, audio').length) scanVideos(); }, 2000);
  }
  window.addEventListener('pagehide', () => { clearInterval(playerPoll); playerPoll = null; });
  window.addEventListener('pageshow', startPlayerPoll);
  startPlayerPoll();
  function ready() { discoverShadowRoots(document); mount(); scanVideos(); scanPageSources(); askFrames(); }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', ready, { once: true });
  else ready();
  function onMutations(mutations) {
    let relevant = false;
    for (const mutation of mutations) {
      if (mutation.type === 'attributes' && mutation.target.matches?.('video, audio, source, track, iframe, frame, script, link, meta')) relevant = true;
      for (const removed of mutation.removedNodes || []) {
        if (removed.nodeType === 1 && (removed.matches?.('video, audio, source') || removed.querySelector?.('video, audio, source') || removed.shadowRoot)) relevant = true;
      }
      for (const added of mutation.addedNodes || []) {
        if (added.nodeType === 1) {
          discoverShadowRoots(added);
          if (added.matches?.('video, audio, source, track, iframe, frame, script, link, meta') || added.querySelector?.('video, audio, source, track, iframe, frame, script, link, meta')) relevant = true;
        }
      }
    }
    if (relevant) { scanVideos(); scanPageSources(); askFrames(); }
    if (!ui && isTop) mount();
  }
})();
