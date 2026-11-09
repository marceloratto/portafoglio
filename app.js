/* =====================================================================
   Portafoglio (web) — finanças da família, cifrado de ponta a ponta
   Cada item é cifrado (AES-256-GCM) no aparelho antes de ir ao Firebase.
   Chave compartilhada: embrulhada pela senha do cofre de cada usuário.
   Chave privada: só do usuário (itens marcados "só eu vejo").
   ===================================================================== */
import { initializeApp } from './vendor/firebase-app.js';
import { getAuth, onAuthStateChanged, signInWithEmailAndPassword, createUserWithEmailAndPassword, sendEmailVerification, sendPasswordResetEmail, signOut, getMultiFactorResolver, TotpMultiFactorGenerator, multiFactor, reauthenticateWithCredential, EmailAuthProvider, updatePassword, connectAuthEmulator } from './vendor/firebase-auth.js';
import { getDatabase, ref, get, set, update, push, query, limitToLast, onChildAdded, onChildChanged, onChildRemoved, runTransaction, connectDatabaseEmulator } from './vendor/firebase-database.js';
import { FIREBASE_CONFIG } from './firebase-config.js';
const VERSAO = 'web 1.0';
const PBKDF2_ITER = 600000;
/* ---------------- utilidades ---------------- */
const $ = s => document.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const uid = () => Math.random().toString(36).slice(2, 9) + Date.now().toString(36).slice(-4);
const fmtR = v => (v < 0 ? '-' : '') + 'R$ ' + Math.abs(v || 0).toLocaleString('pt-BR', {minimumFractionDigits: 2, maximumFractionDigits: 2});
const fmtN = (v, d = 0) => (v || 0).toLocaleString('pt-BR', {minimumFractionDigits: d, maximumFractionDigits: d});
const fmtPct = v => (isFinite(v) ? (v * 100).toLocaleString('pt-BR', {maximumFractionDigits: 1}) : '–') + '%';
const hoje = () => { const d = new Date(); return ymd(d); };
const ymd = d => d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0');
const mesAtual = () => hoje().slice(0, 7);
const MESES = ['janeiro','fevereiro','março','abril','maio','junho','julho','agosto','setembro','outubro','novembro','dezembro'];
const MESES_AB = ['JAN','FEV','MAR','ABR','MAI','JUN','JUL','AGO','SET','OUT','NOV','DEZ'];
const nomeMes = m => { const [y, mm] = m.split('-'); return MESES[+mm - 1] + ' ' + y; };
const nomeMesCurto = m => { const [y, mm] = m.split('-'); return MESES_AB[+mm - 1] + '/' + y.slice(2); };
const addMes = (m, n) => { let [y, mm] = m.split('-').map(Number); mm += n; while (mm > 12) { mm -= 12; y++; } while (mm < 1) { mm += 12; y--; } return y + '-' + String(mm).padStart(2, '0'); };
const fmtData = d => d ? d.split('-').reverse().join('/') : '';
const diasEntre = (a, b) => Math.round((new Date(b + 'T12:00') - new Date(a + 'T12:00')) / 86400000);
const norm = s => String(s || '').normalize('NFD').replace(/[̀-ͯ]/g, '').toUpperCase().replace(/\s+/g, ' ').trim();
function parseBR(s) {
  if (typeof s === 'number') return s;
  s = String(s || '').replace(/[R$\s]/g, '').replace(/[−–]/g, '-');
  if (!s) return 0;
  let neg = /^-|-$/.test(s); s = s.replace(/-/g, '');
  if (s.includes(',')) s = s.replace(/\./g, '').replace(',', '.');
  const v = parseFloat(s); return isNaN(v) ? 0 : (neg ? -v : v);
}
const b64 = buf => btoa(String.fromCharCode(...new Uint8Array(buf)));
const unb64 = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
const enc = s => new TextEncoder().encode(s);
function toast(msg, ms = 2600) { const t = $('#toast'); t.textContent = msg; t.classList.remove('hidden'); clearTimeout(t._t); t._t = setTimeout(() => t.classList.add('hidden'), ms); }

/* ---------------- criptografia ---------------- */
async function kekDe(senha, salt, iter) {
  const base = await crypto.subtle.importKey('raw', enc(senha), 'PBKDF2', false, ['deriveKey']);
  return crypto.subtle.deriveKey({name: 'PBKDF2', salt, iterations: iter, hash: 'SHA-256'}, base, {name: 'AES-GCM', length: 256}, false, ['encrypt', 'decrypt']);
}
async function embrulhar(rawKey, senha) {
  const salt = crypto.getRandomValues(new Uint8Array(16)), iv = crypto.getRandomValues(new Uint8Array(12));
  const kek = await kekDe(senha, salt, PBKDF2_ITER);
  const w = await crypto.subtle.encrypt({name: 'AES-GCM', iv}, kek, rawKey);
  return {salt: b64(salt), iv: b64(iv), iter: PBKDF2_ITER, chave: b64(w)};
}
async function desembrulhar(u, senha) {
  const kek = await kekDe(senha, unb64(u.salt), u.iter);
  return new Uint8Array(await crypto.subtle.decrypt({name: 'AES-GCM', iv: unb64(u.iv)}, kek, unb64(u.chave)));
}
async function importarChave(raw) { return crypto.subtle.importKey('raw', raw, 'AES-GCM', false, ['encrypt', 'decrypt']); }
async function cifrar(chave, obj) {
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const ct = await crypto.subtle.encrypt({name: 'AES-GCM', iv}, chave, enc(JSON.stringify(obj)));
  return {iv: b64(iv), dados: b64(ct)};
}
async function decifrar(chave, env) {
  const pt = await crypto.subtle.decrypt({name: 'AES-GCM', iv: unb64(env.iv)}, chave, unb64(env.dados));
  return JSON.parse(new TextDecoder().decode(pt));
}

/* ---------------- estado inicial ---------------- */
function estadoNovo(nomes) {
  const pessoas = nomes.map(n => ({id: uid(), nome: n}));
  const cats = [
    ['Moradia', 'despesa', '#141414'], ['Contas de consumo', 'despesa', '#3b3b40'], ['Mercado', 'despesa', '#d0232b'],
    ['Restaurantes e delivery', 'despesa', '#e0575d'], ['Transporte e combustível', 'despesa', '#6b6b73'], ['Saúde e farmácia', 'despesa', '#1f8a4c'],
    ['Educação', 'despesa', '#2f6db3'], ['Filhos', 'despesa', '#8e44ad'], ['Lazer', 'despesa', '#c98a00'], ['Viagens', 'despesa', '#0e8a8a'],
    ['Vestuário', 'despesa', '#b05d2c'], ['Assinaturas', 'despesa', '#5a4fcf'], ['Compras', 'despesa', '#a1a1aa'], ['Impostos, taxas e juros', 'despesa', '#7a1a1e'],
    ['Seguros', 'despesa', '#4a6572'], ['Pets', 'despesa', '#9c7a4d'], ['Presentes e doações', 'despesa', '#c2185b'], ['Outros', 'despesa', '#c4c4c9'],
    ['Salário / pró-labore', 'receita', '#1f8a4c'], ['Rendimentos', 'receita', '#2e9e5e'], ['Outras receitas', 'receita', '#64b88a'],
    ['Aporte em investimentos', 'reserva', '#141414'], ['Pagamento de fatura', 'neutro', '#a1a1aa'], ['Transferência entre contas', 'neutro', '#c4c4c9'],
  ].map(([nome, tipo, cor]) => ({id: uid(), nome, tipo, cor, limite: 0}));
  const c = n => cats.find(x => x.nome === n).id;
  const regras = [
    ['IFOOD', 'Restaurantes e delivery'], ['RAPPI', 'Restaurantes e delivery'], ['RESTAURANTE', 'Restaurantes e delivery'], ['PADARIA', 'Restaurantes e delivery'],
    ['UBER', 'Transporte e combustível'], ['POSTO', 'Transporte e combustível'], ['SHELL', 'Transporte e combustível'], ['IPIRANGA', 'Transporte e combustível'], ['PETROBRAS', 'Transporte e combustível'], ['ESTACIONAMENTO', 'Transporte e combustível'], ['SEM PARAR', 'Transporte e combustível'], ['VELOE', 'Transporte e combustível'],
    ['SUPERMERC', 'Mercado'], ['MERCADO', 'Mercado'], ['ZONA SUL', 'Mercado'], ['PAO DE ACUCAR', 'Mercado'], ['ASSAI', 'Mercado'], ['CARREFOUR', 'Mercado'], ['PREZUNIC', 'Mercado'], ['GUANABARA', 'Mercado'], ['HORTIFRUTI', 'Mercado'], ['ATACAD', 'Mercado'],
    ['DROGA', 'Saúde e farmácia'], ['FARMACIA', 'Saúde e farmácia'], ['PACHECO', 'Saúde e farmácia'], ['RAIA', 'Saúde e farmácia'], ['VENANCIO', 'Saúde e farmácia'], ['UNIMED', 'Saúde e farmácia'], ['AMIL', 'Saúde e farmácia'], ['BRADESCO SAUDE', 'Saúde e farmácia'], ['LABORATORIO', 'Saúde e farmácia'],
    ['NETFLIX', 'Assinaturas'], ['SPOTIFY', 'Assinaturas'], ['DISNEY', 'Assinaturas'], ['PRIME VIDEO', 'Assinaturas'], ['AMAZON PRIME', 'Assinaturas'], ['YOUTUBE', 'Assinaturas'], ['APPLE.COM', 'Assinaturas'], ['GOOGLE ONE', 'Assinaturas'], ['GLOBOPLAY', 'Assinaturas'], ['MAX ', 'Assinaturas'], ['CLAUDE', 'Assinaturas'], ['OPENAI', 'Assinaturas'],
    ['LIGHT ', 'Contas de consumo'], ['ENEL', 'Contas de consumo'], ['CEDAE', 'Contas de consumo'], ['AGUAS DO', 'Contas de consumo'], ['NATURGY', 'Contas de consumo'], ['CEG ', 'Contas de consumo'], ['CLARO', 'Contas de consumo'], ['VIVO', 'Contas de consumo'], ['TIM ', 'Contas de consumo'], ['NET SERVICOS', 'Contas de consumo'],
    ['IOF', 'Impostos, taxas e juros'], ['ANUIDADE', 'Impostos, taxas e juros'], ['JUROS', 'Impostos, taxas e juros'], ['TARIFA', 'Impostos, taxas e juros'], ['ENCARGO', 'Impostos, taxas e juros'], ['MULTA', 'Impostos, taxas e juros'], ['IPVA', 'Impostos, taxas e juros'], ['IPTU', 'Impostos, taxas e juros'], ['DARF', 'Impostos, taxas e juros'],
    ['LATAM', 'Viagens'], ['GOL LINHAS', 'Viagens'], ['AZUL LINHAS', 'Viagens'], ['BOOKING', 'Viagens'], ['AIRBNB', 'Viagens'], ['HOTEL', 'Viagens'], ['DECOLAR', 'Viagens'], ['POUSADA', 'Viagens'],
    ['ESCOLA', 'Educação'], ['COLEGIO', 'Educação'], ['FACULDADE', 'Educação'], ['UNIVERSIDADE', 'Educação'], ['CURSO', 'Educação'], ['LIVRARIA', 'Educação'],
    ['PET', 'Pets'], ['PORTO SEGURO', 'Seguros'], ['SEGURO', 'Seguros'], ['CONDOMINIO', 'Moradia'], ['ALUGUEL', 'Moradia'],
    ['PAGAMENTO EFETUADO', 'Pagamento de fatura'], ['PAGAMENTO RECEBIDO', 'Pagamento de fatura'], ['PAGTO FATURA', 'Pagamento de fatura'], ['PAG FATURA', 'Pagamento de fatura'], ['PAGAMENTO FATURA', 'Pagamento de fatura'], ['PAGAMENTO DE FATURA', 'Pagamento de fatura'], ['FATURA CARTAO', 'Pagamento de fatura'], ['INT PAG TIT', 'Pagamento de fatura'],
    ['APLICACAO', 'Aporte em investimentos'], ['APLIC ', 'Aporte em investimentos'], ['RESGATE', 'Rendimentos'], ['RENDIMENTO', 'Rendimentos'], ['DIVIDENDO', 'Rendimentos'], ['SALARIO', 'Salário / pró-labore'], ['PRO LABORE', 'Salário / pró-labore'], ['PRO-LABORE', 'Salário / pró-labore'],
  ].map(([termo, cat]) => ({id: uid(), termo, cat: c(cat)}));
  return {
    versao: 1, criadoEm: new Date().toISOString(), pessoas, categorias: cats, regras, chavesSync: null,
    contas: [], lancamentos: [], fixas: [], pagFixas: {}, filhos: [], cobrancas: {}, milhas: [], investimentos: [], metas: [],
    config: {bloqueioMin: 10, ultimoBackup: null,
      msgWhats: 'Oi {nome}! Tudo bem? Me manda, por favor, as contas de {mes} para eu pagar:\n{lista}\nObrigado! 😊'},
  };
}

/* ---------------- Firebase ---------------- */
const fbApp = initializeApp(FIREBASE_CONFIG);
const auth = getAuth(fbApp);
const db = getDatabase(fbApp);
if (window.PF_EMULADOR) { connectAuthEmulator(auth, 'http://127.0.0.1:9099', {disableWarnings: true}); connectDatabaseEmulator(db, '127.0.0.1', 9000); }
const R = p => ref(db, 'pf/' + p);
const COLS_ARR = ['pessoas', 'categorias', 'regras', 'contas', 'lancamentos', 'fixas', 'filhos', 'milhas', 'investimentos', 'metas'];
const COLS_MAP = ['pagFixas', 'cobrancas'];
const COLS_PRIV = ['contas', 'lancamentos', 'fixas', 'milhas', 'investimentos', 'metas'];
const TODAS_COLS = [...COLS_ARR, ...COLS_MAP, 'cfg'];
const ORDEM_TIPO = {despesa: 0, receita: 1, reserva: 2, neutro: 3};

/* ---------------- sessão ---------------- */
let S = null;          // estado decifrado
let CHAVE = null;      // chave compartilhada (AES)
let PCHAVE = null;     // chave privada do usuário (AES) — itens "só eu vejo"
let RAW = null;        // chave compartilhada crua (para convites e troca de senha)
let PRAW = null;       // chave privada crua
let USER = null;       // {uid, nome, pessoa, email}
let COFRE = null;      // /pf/cofre/usuarios
let SNAP = new Map();  // col/id -> {j, p}  (último estado gravado/recebido)
let OUVINTES = [];
let renderPendente = false;
const ui = {view: 'painel', mes: mesAtual(), pessoa: 'todos', filtro: {}};

async function encItem(k, obj) { const c = await cifrar(k, obj); return {iv: c.iv, d: c.dados}; }
async function decItem(k, v) { return decifrar(k, {iv: v.iv, dados: v.d}); }
const caminho = (col, id, priv) => (priv ? `privado/${USER.uid}/dados/` : 'dados/') + col + '/' + id;

function estadoVazio() { const s = {config: {}, chavesSync: null}; COLS_ARR.forEach(c => s[c] = []); COLS_MAP.forEach(c => s[c] = {}); return s; }
function aplicarNoEstado(col, id, obj) {
  if (col === 'cfg') { if (id === 'config') S.config = obj; else if (id === 'sync') S.chavesSync = obj; return; }
  if (COLS_MAP.includes(col)) { S[col][id] = obj; return; }
  const arr = S[col]; if (!arr) return; const i = arr.findIndex(x => x.id === id);
  if (i >= 0) arr[i] = obj; else arr.push(obj);
}
function removerDoEstado(col, id) {
  if (col === 'cfg') return;
  if (COLS_MAP.includes(col)) { delete S[col][id]; return; }
  if (S[col]) S[col] = S[col].filter(x => x.id !== id);
}
function ordenarEstado() {
  S.categorias.sort((a, b) => (ORDEM_TIPO[a.tipo] ?? 9) - (ORDEM_TIPO[b.tipo] ?? 9) || (a.o ?? 999) - (b.o ?? 999) || a.nome.localeCompare(b.nome));
  S.pessoas.sort((a, b) => (a.o ?? 0) - (b.o ?? 0));
  S.contas.sort((a, b) => a.nome.localeCompare(b.nome));
}

/* grava somente o que mudou (cada item cifrado separadamente) */
let salvarT = null, salvando = Promise.resolve();
function salvar(imediato) {
  clearTimeout(salvarT);
  const go = () => { salvando = salvando.then(salvarAgora).catch(e => { console.error(e); toast('Falha ao salvar: ' + (e.code || e.message), 6000); }); };
  if (imediato) go(); else salvarT = setTimeout(go, 400);
  return salvando;
}
async function salvarAgora() {
  if (!S || !CHAVE) return;
  const atual = new Map();
  const contaPriv = {}; S.contas.forEach(c => { if (c.privado) contaPriv[c.id] = c.privado; });
  for (const col of COLS_ARR) for (const o of S[col]) {
    if (!o.id) o.id = uid();
    if (col === 'lancamentos' && o.conta && contaPriv[o.conta]) o.privado = contaPriv[o.conta];
    if (!COLS_PRIV.includes(col)) delete o.privado;
    if (o.privado && o.privado !== USER.uid) continue; // nunca acontece: itens privados de outros não são carregados
    atual.set(col + '/' + o.id, {col, id: o.id, o, priv: !!o.privado});
  }
  for (const col of COLS_MAP) for (const k of Object.keys(S[col])) atual.set(col + '/' + k, {col, id: k, o: S[col][k], priv: false});
  atual.set('cfg/config', {col: 'cfg', id: 'config', o: S.config, priv: false});
  if (S.chavesSync) atual.set('cfg/sync', {col: 'cfg', id: 'sync', o: S.chavesSync, priv: false});
  const upd = {};
  for (const [k, v] of atual) {
    const j = JSON.stringify(v.o), p = caminho(v.col, v.id, v.priv), old = SNAP.get(k);
    if (old && old.j === j && old.p === p) continue;
    upd[p] = await encItem(v.priv ? PCHAVE : CHAVE, v.o);
    if (old && old.p !== p) upd[old.p] = null;
    SNAP.set(k, {j, p});
  }
  for (const [k, old] of [...SNAP]) if (!atual.has(k)) { upd[old.p] = null; SNAP.delete(k); }
  if (Object.keys(upd).length) await update(ref(db, 'pf'), upd);
}

/* recebe alterações feitas no outro aparelho / pelo outro usuário */
function ouvir() {
  desligarOuvintes();
  const bases = [['dados/', false], [`privado/${USER.uid}/dados/`, true]];
  for (const [base, priv] of bases) for (const col of TODAS_COLS) {
    const r = R(base + col);
    OUVINTES.push(onChildAdded(r, s => remoto(col, s.key, s.val(), priv, false)));
    OUVINTES.push(onChildChanged(r, s => remoto(col, s.key, s.val(), priv, false)));
    OUVINTES.push(onChildRemoved(r, s => remoto(col, s.key, null, priv, true)));
  }
  OUVINTES.push(onChildAdded(R('sync/inbox'), s => consumirSync(s.key)));
}
function desligarOuvintes() { OUVINTES.forEach(f => { try { f(); } catch (e) {} }); OUVINTES = []; }
async function remoto(col, id, val, priv, removido) {
  if (!S) return;
  const k = col + '/' + id, p = caminho(col, id, priv), old = SNAP.get(k);
  if (removido) { if (old && old.p === p) { SNAP.delete(k); removerDoEstado(col, id); agendarRender(); } return; }
  let obj; try { obj = await decItem(priv ? PCHAVE : CHAVE, val); } catch (e) { return; }
  if (!S) return;
  const j = JSON.stringify(obj);
  if (old && old.j === j && old.p === p) return;
  SNAP.set(k, {j, p}); aplicarNoEstado(col, id, obj); agendarRender();
}
function agendarRender() {
  clearTimeout(agendarRender._t);
  agendarRender._t = setTimeout(() => {
    if (!S) return;
    const m = $('#modal'); const digitando = document.activeElement && /INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName);
    if (!m.classList.contains('hidden') || digitando) { renderPendente = true; return; }
    ordenarEstado(); render();
  }, 250);
}
document.addEventListener('focusout', () => { if (renderPendente && $('#modal').classList.contains('hidden')) setTimeout(() => { if (renderPendente && S && !(document.activeElement && /INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName))) { renderPendente = false; ordenarEstado(); render(); } }, 300); });

/* ---------------- telas de acesso ---------------- */
const TOPO_LOCK = () => `<div class="marca"><img class="ico" src="icone-192.png" alt="" style="width:64px;height:64px;border:2px solid #141414"><div><div class="nome" style="font-size:22px">Portafoglio</div><div class="sub">finanças da família · cifrado de ponta a ponta</div></div></div><div class="filete"></div>`;
function lockBox(html) {
  $('#app').classList.add('hidden'); $('#modal').classList.add('hidden'); $('#lock').classList.remove('hidden');
  const b = $('#lockbox'); b.innerHTML = TOPO_LOCK() + html; return b;
}
function botaoSair(b) { const s = b.querySelector('#lnksair'); if (s) s.onclick = e => { e.preventDefault(); sair(); }; }
const SAIR = `<p class="small muted" style="margin-top:14px"><a href="#" id="lnksair">Sair desta conta</a></p>`;
function erroAuth(e) {
  const c = e.code || '';
  if (/invalid-credential|wrong-password|user-not-found|invalid-login/.test(c)) return 'E-mail ou senha incorretos.';
  if (/too-many-requests/.test(c)) return 'Muitas tentativas. Aguarde alguns minutos.';
  if (/email-already-in-use/.test(c)) return 'Este e-mail já tem acesso. Use "Entrar".';
  if (/weak-password/.test(c)) return 'Senha fraca: use pelo menos 8 caracteres.';
  if (/invalid-email/.test(c)) return 'E-mail inválido.';
  if (/network/.test(c)) return 'Sem conexão com a internet.';
  if (/invalid-verification-code/.test(c)) return 'Código incorreto.';
  return 'Erro: ' + (c || e.message);
}
function telaLogin(msg) {
  limparSessao();
  const b = lockBox(`<h1>Entrar</h1><p>${esc(msg || 'Use o e-mail liberado para o Portafoglio.')}</p>
    <div class="fld"><label>E-mail</label><input class="in" id="le" type="email" autocomplete="username"></div>
    <div class="fld"><label>Senha de acesso</label><input class="in" id="lp" type="password" autocomplete="current-password"></div>
    <button class="btn pri" id="lent" style="width:100%;justify-content:center;padding:10px">Entrar</button>
    <div class="erro" id="err"></div>
    <p class="small" style="margin-top:12px"><a href="#" id="lcri">Primeiro acesso? Criar meu login</a> · <a href="#" id="lesq">Esqueci a senha</a></p>`);
  const ir = async () => {
    const err = b.querySelector('#err'); err.textContent = 'Entrando…'; b.querySelector('#lent').disabled = true;
    try { await signInWithEmailAndPassword(auth, b.querySelector('#le').value.trim(), b.querySelector('#lp').value); }
    catch (e) {
      if (e.code === 'auth/multi-factor-auth-required') return telaCodigo2FA(getMultiFactorResolver(auth, e));
      err.textContent = erroAuth(e); b.querySelector('#lent').disabled = false;
    }
  };
  b.querySelector('#lent').onclick = ir; b.querySelector('#lp').onkeydown = e => { if (e.key === 'Enter') ir(); };
  b.querySelector('#lesq').onclick = async e => { e.preventDefault(); const em = b.querySelector('#le').value.trim(); const err = b.querySelector('#err');
    if (!em) return err.textContent = 'Digite seu e-mail acima e clique de novo em "Esqueci a senha".';
    try { await sendPasswordResetEmail(auth, em); err.style.color = 'var(--verde)'; err.textContent = 'Se o e-mail estiver cadastrado, você vai receber um link para criar nova senha.'; } catch (x) { err.textContent = erroAuth(x); } };
  b.querySelector('#lcri').onclick = e => { e.preventDefault(); telaCriarLogin(); };
  setTimeout(() => b.querySelector('#le').focus(), 50);
}
function telaCriarLogin() {
  const b = lockBox(`<h1>Criar meu login</h1><p>Só funciona para e-mails liberados no Portafoglio. Depois de criar, confirme o e-mail pelo link que vai chegar.</p>
    <div class="fld"><label>E-mail</label><input class="in" id="ce" type="email" autocomplete="username"></div>
    <div class="fld"><label>Senha de acesso (mín. 10 caracteres)</label><input class="in" id="cp" type="password" autocomplete="new-password"></div>
    <div class="fld"><label>Repita</label><input class="in" id="cp2" type="password" autocomplete="new-password"></div>
    <button class="btn pri" id="cok" style="width:100%;justify-content:center;padding:10px">Criar login</button><div class="erro" id="err"></div>
    <p class="small" style="margin-top:12px"><a href="#" id="cvolta">Voltar</a></p>`);
  b.querySelector('#cvolta').onclick = e => { e.preventDefault(); telaLogin(); };
  b.querySelector('#cok').onclick = async () => {
    const err = b.querySelector('#err'), p = b.querySelector('#cp').value;
    if (p.length < 10) return err.textContent = 'Use pelo menos 10 caracteres.';
    if (p !== b.querySelector('#cp2').value) return err.textContent = 'As senhas não conferem.';
    try { const c = await createUserWithEmailAndPassword(auth, b.querySelector('#ce').value.trim(), p); await sendEmailVerification(c.user); }
    catch (e) { err.textContent = erroAuth(e); }
  };
}
function telaCodigo2FA(resolver) {
  const hint = resolver.hints.find(h => h.factorId === TotpMultiFactorGenerator.FACTOR_ID) || resolver.hints[0];
  const b = lockBox(`<h1>Verificação em duas etapas</h1><p>Digite o código de 6 dígitos do seu app autenticador.</p>
    <div class="fld"><input class="in" id="tc" inputmode="numeric" maxlength="6" autocomplete="one-time-code" style="font-size:22px;letter-spacing:6px;text-align:center"></div>
    <button class="btn pri" id="tok" style="width:100%;justify-content:center;padding:10px">Confirmar</button><div class="erro" id="err"></div>
    <p class="small" style="margin-top:12px"><a href="#" id="tvolta">Voltar</a></p>`);
  const ir = async () => {
    try { await resolver.resolveSignIn(TotpMultiFactorGenerator.assertionForSignIn(hint.uid, b.querySelector('#tc').value.trim())); }
    catch (e) { b.querySelector('#err').textContent = erroAuth(e); }
  };
  b.querySelector('#tok').onclick = ir; b.querySelector('#tc').onkeydown = e => { if (e.key === 'Enter') ir(); };
  b.querySelector('#tvolta').onclick = e => { e.preventDefault(); telaLogin(); };
  setTimeout(() => b.querySelector('#tc').focus(), 50);
}
function telaVerificarEmail(user) {
  const b = lockBox(`<h1>Confirme seu e-mail</h1><p>Enviamos um link para <b>${esc(user.email)}</b>. Clique nele e depois volte aqui.</p>
    <div class="ctrl"><button class="btn pri" id="vjá">Já confirmei</button><button class="btn" id="vre">Reenviar e-mail</button></div><div class="erro" id="err"></div>` + SAIR);
  b.querySelector('#vjá').onclick = async () => { await user.reload(); if (auth.currentUser.emailVerified) { await auth.currentUser.getIdToken(true); posLogin(auth.currentUser); } else b.querySelector('#err').textContent = 'Ainda não consta como confirmado.'; };
  b.querySelector('#vre').onclick = async () => { try { await sendEmailVerification(user); b.querySelector('#err').textContent = 'Reenviado.'; } catch (e) { b.querySelector('#err').textContent = erroAuth(e); } };
  botaoSair(b);
}
async function posLogin(user) {
  if (!user.emailVerified) return telaVerificarEmail(user);
  lockBox('<p>Carregando…</p>');
  let us;
  try { us = (await get(R('cofre/usuarios'))).val(); }
  catch (e) {
    const b = lockBox(`<h1>Acesso não liberado</h1><p>O e-mail <b>${esc(user.email)}</b> ainda não está autorizado no Portafoglio.</p><p class="small muted">Quem administra precisa incluí-lo na lista de membros do Firebase (veja o guia de instalação, passo "Liberar e-mails").</p>` + SAIR);
    return botaoSair(b);
  }
  COFRE = us || {};
  if (!us || !Object.keys(us).length) return telaCriarCofre(user);
  if (!us[user.uid]) return telaConvite(user);
  telaDesbloquear(user);
}
function senhaForteMsg(s) { if (s.length < 10) return 'A senha do cofre precisa ter pelo menos 10 caracteres. Uma frase longa é o ideal (ex.: cafe-azul-serra-42).'; return ''; }
function telaCriarCofre(user) {
  const b = lockBox(`<h1>Criar o cofre</h1><p>Esta é a <b>senha do cofre</b>: ela decifra os dados no seu aparelho e nunca é enviada para a internet. Use uma frase longa, diferente da senha de acesso.</p>
    <div class="fld"><label>Seu nome</label><input class="in" id="n1" autocomplete="off"></div>
    <div class="fld"><label>Senha do cofre</label><input class="in" id="p1" type="password" autocomplete="new-password"></div>
    <div class="fld"><label>Repita</label><input class="in" id="p1b" type="password" autocomplete="new-password"></div>
    <label class="chk" style="margin-bottom:12px"><input type="checkbox" id="mig"> Trazer os dados do Portafoglio offline (arquivo de backup .portafoglio)</label>
    <div id="migbox" class="hidden"><div class="fld"><label>Arquivo de backup</label><input class="in" type="file" id="mf" accept=".portafoglio,.familia,.json"></div>
      <div class="fld"><label>Senha usada no Portafoglio offline</label><input class="in" id="mp" type="password"></div></div>
    <button class="btn pri" id="bcriar" style="width:100%;justify-content:center;padding:10px">Criar cofre</button><div class="erro" id="err"></div>
    <p class="small muted">Não existe recuperação da senha do cofre. Guarde-a em lugar seguro.</p>` + SAIR);
  botaoSair(b);
  b.querySelector('#mig').onchange = e => b.querySelector('#migbox').classList.toggle('hidden', !e.target.checked);
  b.querySelector('#bcriar').onclick = async () => {
    const err = b.querySelector('#err'); const n = b.querySelector('#n1').value.trim(), p = b.querySelector('#p1').value;
    if (!n) return err.textContent = 'Informe seu nome.';
    const fm = senhaForteMsg(p); if (fm) return err.textContent = fm;
    if (p !== b.querySelector('#p1b').value) return err.textContent = 'As senhas não conferem.';
    let est = null;
    if (b.querySelector('#mig').checked) {
      try {
        const f = b.querySelector('#mf').files[0]; if (!f) return err.textContent = 'Escolha o arquivo de backup.';
        const env = JSON.parse(await f.text()); let ok = null;
        for (const u of env.usuarios || []) { try { const raw = await desembrulhar(u, b.querySelector('#mp').value); ok = await decifrar(await importarChave(raw), env); break; } catch (x) {} }
        if (!ok) return err.textContent = 'Não consegui abrir o backup com essa senha.';
        est = ok;
      } catch (x) { return err.textContent = 'Arquivo inválido.'; }
    }
    err.textContent = 'Gerando chaves…'; b.querySelector('#bcriar').disabled = true;
    try {
      RAW = crypto.getRandomValues(new Uint8Array(32)); PRAW = crypto.getRandomValues(new Uint8Array(32));
      CHAVE = await importarChave(RAW); PCHAVE = await importarChave(PRAW);
      if (!est) est = estadoNovo([n]);
      S = estadoVazio(); Object.assign(S, est); migrar();
      S.pessoas.forEach((p, i) => p.o = i); S.categorias.forEach((c, i) => c.o = i);
      const pessoaId = S.pessoas[0].id; if (est && S.pessoas[0]) S.pessoas[0].nome = S.pessoas[0].nome || n;
      USER = {uid: user.uid, nome: n, pessoa: pessoaId, email: user.email};
      await criarChavesSync();
      const upd = {};
      upd['cofre/usuarios/' + user.uid] = {nome: n, pessoa: pessoaId, criadoEm: new Date().toISOString(), ...(await embrulhar(RAW, p))};
      upd[`privado/${user.uid}/chave`] = await embrulhar(PRAW, p);
      await update(ref(db, 'pf'), upd);
      COFRE = {[user.uid]: upd['cofre/usuarios/' + user.uid]};
      SNAP = new Map(); await salvarAgora();
      entrar();
    } catch (x) { console.error(x); err.textContent = 'Falha: ' + (x.code || x.message); b.querySelector('#bcriar').disabled = false; }
  };
}
async function criarChavesSync() {
  const kp = await crypto.subtle.generateKey({name: 'ECDH', namedCurve: 'P-256'}, true, ['deriveBits']);
  const priv = await crypto.subtle.exportKey('jwk', kp.privateKey), pub = await crypto.subtle.exportKey('jwk', kp.publicKey);
  S.chavesSync = {priv, pub, criadoEm: new Date().toISOString()};
  await set(R('sync/pub'), {kty: pub.kty, crv: pub.crv, x: pub.x, y: pub.y});
}
function telaConvite(user) {
  const b = lockBox(`<h1>Entrar com convite</h1><p>Peça o <b>código de convite</b> a quem administra o Portafoglio. Depois crie a sua <b>senha do cofre</b> (fica só com você).</p>
    <div class="fld"><label>Código de convite</label><input class="in" id="cc" autocomplete="off" style="text-transform:uppercase;letter-spacing:2px"></div>
    <div class="fld"><label>Sua senha do cofre</label><input class="in" id="cs" type="password" autocomplete="new-password"></div>
    <div class="fld"><label>Repita</label><input class="in" id="cs2" type="password" autocomplete="new-password"></div>
    <button class="btn pri" id="cok" style="width:100%;justify-content:center;padding:10px">Ativar meu acesso</button><div class="erro" id="err"></div>` + SAIR);
  botaoSair(b);
  b.querySelector('#cok').onclick = async () => {
    const err = b.querySelector('#err'); const code = normCodigo(b.querySelector('#cc').value), s = b.querySelector('#cs').value;
    const fm = senhaForteMsg(s); if (fm) return err.textContent = fm;
    if (s !== b.querySelector('#cs2').value) return err.textContent = 'As senhas não conferem.';
    err.textContent = 'Verificando convite…';
    try {
      const id = await hashCodigo(code); const cv = (await get(R('convites/' + id))).val();
      if (!cv) return err.textContent = 'Convite não encontrado.';
      if (cv.expira < Date.now()) return err.textContent = 'Convite expirado. Peça um novo.';
      let raw; try { raw = await desembrulhar(cv, code); } catch (x) { return err.textContent = 'Código incorreto.'; }
      PRAW = crypto.getRandomValues(new Uint8Array(32));
      const upd = {};
      upd['cofre/usuarios/' + user.uid] = {nome: cv.nome, pessoa: cv.pessoa, criadoEm: new Date().toISOString(), convidadoPor: cv.por || '', ...(await embrulhar(raw, s))};
      upd[`privado/${user.uid}/chave`] = await embrulhar(PRAW, s);
      upd['convites/' + id] = null;
      await update(ref(db, 'pf'), upd);
      COFRE[user.uid] = upd['cofre/usuarios/' + user.uid];
      RAW = raw; CHAVE = await importarChave(raw); PCHAVE = await importarChave(PRAW);
      USER = {uid: user.uid, nome: cv.nome, pessoa: cv.pessoa, email: user.email};
      await carregarDados(); entrar();
    } catch (x) { console.error(x); err.textContent = 'Falha: ' + (x.code || x.message); }
  };
}
const ALFA = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
function gerarCodigo() { const r = crypto.getRandomValues(new Uint8Array(16)); let s = ''; for (let i = 0; i < 16; i++) s += ALFA[r[i] % ALFA.length]; return s.match(/.{4}/g).join('-'); }
const normCodigo = c => c.toUpperCase().replace(/[^A-Z0-9]/g, '').match(/.{1,4}/g)?.join('-') || '';
async function hashCodigo(c) { const h = await crypto.subtle.digest('SHA-256', enc('pf-convite:' + c)); return [...new Uint8Array(h)].map(x => x.toString(16).padStart(2, '0')).join('').slice(0, 32); }

function telaDesbloquear(user, msg) {
  const meu = COFRE[user.uid];
  const b = lockBox(`<h1>Olá, ${esc(meu.nome)}</h1><p>${esc(msg || 'Digite a senha do cofre para abrir seus dados.')}</p>
    <div class="fld"><label>Senha do cofre</label><input class="in" id="pw" type="password" autocomplete="current-password"></div>
    <button class="btn pri" id="bent" style="width:100%;justify-content:center;padding:10px">Desbloquear</button><div class="erro" id="err"></div>` + SAIR);
  botaoSair(b);
  const ir = async () => {
    const err = b.querySelector('#err'); err.textContent = 'Abrindo…'; b.querySelector('#bent').disabled = true;
    const s = b.querySelector('#pw').value;
    try { RAW = await desembrulhar(meu, s); } catch (e) { err.textContent = 'Senha do cofre incorreta.'; b.querySelector('#bent').disabled = false; b.querySelector('#pw').select(); return; }
    try {
      CHAVE = await importarChave(RAW);
      const pk = (await get(R(`privado/${user.uid}/chave`))).val();
      if (pk) PRAW = await desembrulhar(pk, s); else { PRAW = crypto.getRandomValues(new Uint8Array(32)); await set(R(`privado/${user.uid}/chave`), await embrulhar(PRAW, s)); }
      PCHAVE = await importarChave(PRAW);
      USER = {uid: user.uid, nome: meu.nome, pessoa: meu.pessoa, email: user.email};
      await carregarDados(); entrar();
    } catch (e) { console.error(e); err.textContent = 'Falha ao carregar: ' + (e.code || e.message); b.querySelector('#bent').disabled = false; }
  };
  b.querySelector('#bent').onclick = ir; b.querySelector('#pw').onkeydown = e => { if (e.key === 'Enter') ir(); };
  setTimeout(() => b.querySelector('#pw').focus(), 50);
}
async function carregarDados() {
  const [pub, priv] = await Promise.all([get(R('dados')), get(R(`privado/${USER.uid}/dados`))]);
  S = estadoVazio(); SNAP = new Map();
  for (const [snap, isPriv] of [[pub, false], [priv, true]]) {
    const v = snap.val() || {};
    for (const col of Object.keys(v)) for (const id of Object.keys(v[col])) {
      try { const o = await decItem(isPriv ? PCHAVE : CHAVE, v[col][id]); aplicarNoEstado(col, id, o); SNAP.set(col + '/' + id, {j: JSON.stringify(o), p: caminho(col, id, isPriv)}); }
      catch (e) { console.warn('item ilegível', col, id); }
    }
  }
  migrar(); ordenarEstado();
  if (!S.chavesSync) { await criarChavesSync(); salvar(true); }
}
function entrar() {
  $('#lock').classList.add('hidden'); $('#app').classList.remove('hidden'); ultimaAtividade = Date.now();
  ouvir(); registrarAcesso(); render();
}
async function registrarAcesso() {
  try {
    const ua = navigator.userAgent; const disp = /iPhone|iPad/.test(ua) ? 'iPhone/iPad' : /Android/.test(ua) ? 'Android' : /Windows/.test(ua) ? 'Windows' : /Mac/.test(ua) ? 'Mac' : 'Outro';
    const nav = /Edg\//.test(ua) ? 'Edge' : /Chrome\//.test(ua) ? 'Chrome' : /Safari\//.test(ua) ? 'Safari' : /Firefox\//.test(ua) ? 'Firefox' : '';
    let id = null; try { id = localStorage.getItem('pf.aparelho'); if (!id) { id = uid(); localStorage.setItem('pf.aparelho', id); } } catch (e) { id = 'sem-id'; }
    const ant = (await get(query(R('acessos/' + USER.uid), limitToLast(30)))).val() || {};
    const novo = !Object.values(ant).some(a => a.aparelho === id);
    await push(R('acessos/' + USER.uid), {quando: new Date().toISOString(), disp: disp + (nav ? ' · ' + nav : ''), aparelho: id});
    if (novo && Object.keys(ant).length) toast('Primeiro acesso deste aparelho registrado no histórico.', 4000);
  } catch (e) {}
}
function limparSessao() {
  desligarOuvintes(); clearTimeout(salvarT);
  S = null; CHAVE = null; PCHAVE = null; RAW = null; PRAW = null; USER = null; SNAP = new Map(); IMP = null;
  $('#main').innerHTML = '';
}
async function bloquear(msg) { try { await salvar(true); } catch (e) {} const u = auth.currentUser; limparSessao(); if (u) telaDesbloquear(u, msg); else telaLogin(); }
async function sair() { try { if (S) await salvar(true); } catch (e) {} limparSessao(); await signOut(auth); telaLogin('Você saiu.'); }
function migrar() {
  S.config = S.config || {}; S.cobrancas = S.cobrancas || {}; S.pagFixas = S.pagFixas || {};
  COLS_ARR.forEach(k => S[k] = S[k] || []);
  if (!S.config.msgWhats) S.config.msgWhats = 'Oi {nome}! Tudo bem? Me manda, por favor, as contas de {mes} para eu pagar:\n{lista}\nObrigado! 😊';
  if (!S.config.bloqueioMin) S.config.bloqueioMin = 10;
}

/* auto-bloqueio por inatividade e ao esconder o app no celular */
let ultimaAtividade = Date.now(), escondidoEm = null;
['mousemove', 'keydown', 'click', 'touchstart', 'scroll'].forEach(ev => addEventListener(ev, () => ultimaAtividade = Date.now(), {passive: true}));
setInterval(() => { if (S && Date.now() - ultimaAtividade > (S.config.bloqueioMin || 10) * 60000) bloquear('Bloqueado por inatividade.'); }, 15000);
document.addEventListener('visibilitychange', () => {
  if (document.hidden) { escondidoEm = Date.now(); if (S) salvar(true); }
  else if (S && escondidoEm && Date.now() - escondidoEm > 2 * 60000) bloquear('Bloqueado (app ficou em segundo plano).');
});

/* ---------------- sincronização Open Finance (recebe do robô) ---------------- */
async function chaveSync(epk) {
  const priv = await crypto.subtle.importKey('jwk', S.chavesSync.priv, {name: 'ECDH', namedCurve: 'P-256'}, false, ['deriveBits']);
  const pub = await crypto.subtle.importKey('jwk', epk, {name: 'ECDH', namedCurve: 'P-256'}, false, []);
  const bits = await crypto.subtle.deriveBits({name: 'ECDH', public: pub}, priv, 256);
  const hk = await crypto.subtle.importKey('raw', bits, 'HKDF', false, ['deriveKey']);
  return crypto.subtle.deriveKey({name: 'HKDF', hash: 'SHA-256', salt: new Uint8Array(0), info: enc('portafoglio-sync')}, hk, {name: 'AES-GCM', length: 256}, false, ['decrypt']);
}
async function consumirSync(key) {
  if (!S || !S.chavesSync) return;
  let val = null;
  const r = await runTransaction(R('sync/inbox/' + key), cur => { if (cur === null) return; val = cur; return null; }, {applyLocally: false}).catch(() => null);
  if (!r || !r.committed || !val) return;
  try {
    const k = await chaveSync(val.epk);
    const pt = await crypto.subtle.decrypt({name: 'AES-GCM', iv: unb64(val.iv)}, k, unb64(val.d));
    aplicarSync(JSON.parse(new TextDecoder().decode(pt)));
  } catch (e) { console.error(e); toast('Não consegui ler um pacote da sincronização.', 5000); }
}
const CAT_PLUGGY = [
  [/grocer|supermarket|supermercado/i, 'Mercado'], [/restaurant|eating|food delivery|delivery|bakery|padaria|bar/i, 'Restaurantes e delivery'],
  [/gas station|fuel|taxi|ride|transport|parking|toll|pedágio|vehicle|auto/i, 'Transporte e combustível'],
  [/pharma|drugstore|health|hospital|clinic|dentist|laborat|medic/i, 'Saúde e farmácia'],
  [/education|school|university|course|books/i, 'Educação'], [/stream|digital service|software|subscription|music|video/i, 'Assinaturas'],
  [/travel|airline|airport|hotel|accommodation|accomodation|lodging|tour/i, 'Viagens'], [/cloth|apparel|shoe/i, 'Vestuário'],
  [/electricity|water|gas\b|telecom|internet|mobile|phone|utilities/i, 'Contas de consumo'], [/rent|housing|condo|home/i, 'Moradia'],
  [/insurance/i, 'Seguros'], [/pet|vet/i, 'Pets'], [/tax|interest|fee|iof|fine|bank fees/i, 'Impostos, taxas e juros'],
  [/gift|donation|charity/i, 'Presentes e doações'], [/leisure|entertainment|gym|fitness|sport|games|cinema/i, 'Lazer'],
  [/credit card payment|card payment/i, 'Pagamento de fatura'], [/same person transfer|transfer between/i, 'Transferência entre contas'],
  [/salary|payroll|wage/i, 'Salário / pró-labore'], [/investment|savings|application/i, 'Aporte em investimentos'], [/income|yield|dividend|interest received/i, 'Rendimentos'],
  [/shopping|electronics|department|online/i, 'Compras'],
];
function catPluggy(c) { if (!c) return ''; for (const [re, n] of CAT_PLUGGY) if (re.test(c)) { const x = S.categorias.find(k => k.nome === n); if (x) return x.id; } return ''; }
function mesFatura(c, data) {
  let m = data.slice(0, 7); const d = +data.slice(8, 10);
  if (c && c.fechamento && c.vencimento) { if (d > c.fechamento) m = addMes(m, 1); if (c.vencimento <= c.fechamento) m = addMes(m, 1); }
  return m;
}
function aplicarSync(pl) {
  S.config.mapaPluggy = S.config.mapaPluggy || {};
  S.config.pluggy = {geradoEm: pl.geradoEm, itens: pl.itens || []};
  const mapa = S.config.mapaPluggy; let novasContas = 0;
  for (const a of pl.contas || []) {
    if (mapa[a.id] && conta(mapa[a.id])) continue;
    const tipo = a.type === 'CREDIT' ? 'cartao' : 'banco'; const fin = String(a.number || '').replace(/\D/g, '').slice(-4);
    let c = S.contas.find(x => x.tipo === tipo && fin && x.final === fin && !Object.values(mapa).includes(x.id));
    if (!c) {
      c = {id: uid(), tipo, nome: (a.marketingName || a.name || 'Conta') + (fin ? ' ' + fin : ''), banco: a.banco || '', final: fin, dono: a.dono || S.pessoas[0]?.id || 'casal', origem: 'openfinance'};
      if (a.credito) { if (a.credito.fechamento) c.fechamento = a.credito.fechamento; if (a.credito.vencimento) c.vencimento = a.credito.vencimento; if (a.credito.limite) c.limite = a.credito.limite; }
      S.contas.push(c); novasContas++;
    }
    mapa[a.id] = c.id;
    if (a.saldo != null) c.saldoBanco = {valor: a.saldo, em: pl.geradoEm};
  }
  const vistos = new Set(S.lancamentos.filter(l => l.pluggyId).map(l => l.pluggyId));
  const porChave = new Map(S.lancamentos.filter(l => !l.pluggyId).map(l => [chaveDup(l.conta, l), l]));
  let n = 0, vinc = 0;
  for (const t of pl.transacoes || []) {
    if (t.status && t.status !== 'POSTED') continue;
    if (vistos.has(t.id)) continue;
    const contaId = mapa[t.accountId]; const c = conta(contaId); if (!c) continue;
    const valor = Math.round(Math.abs(t.amount) * 100) / 100 * (t.type === 'DEBIT' ? -1 : 1);
    const data = String(t.date).slice(0, 10), desc = (t.description || '').replace(/\s{2,}/g, ' ').trim();
    const ex = porChave.get(chaveDup(contaId, {data, valor, desc}));
    if (ex) { ex.pluggyId = t.id; vinc++; vistos.add(t.id); continue; }
    const mesRef = c.tipo === 'cartao' ? (t.cc?.billForecastDate && /^\d{4}-\d{2}$/.test(t.cc.billForecastDate) ? t.cc.billForecastDate : mesFatura(c, data)) : data.slice(0, 7);
    const parcela = t.cc?.totalInstallments > 1 ? `${t.cc.installmentNumber || 1}/${t.cc.totalInstallments}` : '';
    S.lancamentos.push({id: uid(), data, mesRef, desc, valor, cat: aplicarRegras(desc) || catPluggy(t.category), conta: contaId, parcela, origem: 'banco', pluggyId: t.id, autor: 'Sincronização'});
    vistos.add(t.id); n++;
  }
  salvar(); ordenarEstado(); agendarRender();
  if (n || novasContas) toast(`Banco sincronizado: ${n} lançamento(s) novo(s)` + (novasContas ? ` · ${novasContas} conta(s)/cartão(ões) adicionados` : ''), 5000);
}
/* ---------------- navegação ---------------- */
const NAV = [
  ['painel', '◉', 'Painel'], ['resumo', '▤', 'Resumo mensal'], ['lancamentos', '≡', 'Lançamentos'], ['importar', '⇪', 'Importar faturas/extratos'],
  '-', ['fixas', '↻', 'Contas fixas'], ['filhos', '☺', 'Cobrança dos filhos'], ['contas', '▭', 'Cartões e contas'], ['milhas', '✈', 'Milhas e pontos'],
  '-', ['investimentos', '▲', 'Investimentos'], ['metas', '◎', 'Reservas e metas'], '-', ['config', '⚙', 'Configurações'],
];
function render() {
  $('#nav').innerHTML = NAV.map(n => n === '-' ? '<div class="sep"></div>' : `<button data-v="${n[0]}" class="${ui.view === n[0] ? 'on' : ''}"><span class="ic">${n[1]}</span>${n[2]}</button>`).join('');
  $('#nav').querySelectorAll('button').forEach(b => b.onclick = () => { ui.view = b.dataset.v; $('#side').classList.remove('aberto'); render(); scrollTo(0, 0); });
  $('#rod').innerHTML = `Conectado: <b>${esc(USER.nome)}</b><br><a href="#" id="blq" style="color:#fff">Bloquear</a> · <a href="#" id="bsair" style="color:#fff">Sair</a><div style="margin-top:8px">Cifrado de ponta a ponta · ${VERSAO}</div>`;
  $('#blq').onclick = e => { e.preventDefault(); bloquear('Bloqueado.'); };
  $('#bsair').onclick = e => { e.preventDefault(); sair(); };
  $('#menu').onclick = () => $('#side').classList.toggle('aberto');
  $('#fab').onclick = lancamentoRapido;
  $('#fab').classList.toggle('hidden', ui.view === 'importar');
  const V = {painel: vPainel, resumo: vResumo, lancamentos: vLanc, importar: vImportar, fixas: vFixas, filhos: vFilhos, contas: vContas, milhas: vMilhas, investimentos: vInvest, metas: vMetas, config: vConfig};
  $('#main').innerHTML = ''; (V[ui.view] || vPainel)($('#main'));
}
function topo(titulo, {mes = false, pessoa = true, extra = ''} = {}) {
  const pes = pessoa && S.pessoas.length > 1 ? `<div class="seg" id="segp"><button data-p="todos" class="${ui.pessoa === 'todos' ? 'on' : ''}">Família</button>${S.pessoas.map(p => `<button data-p="${p.id}" class="${ui.pessoa === p.id ? 'on' : ''}">${esc(p.nome)}</button>`).join('')}</div>` : '';
  const m = mes ? `<div class="mesnav"><button id="mprev">‹</button><span>${nomeMes(ui.mes)}</span><button id="mnext">›</button></div>` : '';
  return `<div class="topo"><h2>${titulo}</h2><div class="ctrl">${pes}${m}${extra}</div></div>`;
}
function ligarTopo(el) {
  el.querySelectorAll('#segp button').forEach(b => b.onclick = () => { ui.pessoa = b.dataset.p; render(); });
  const p = el.querySelector('#mprev'), n = el.querySelector('#mnext');
  if (p) p.onclick = () => { ui.mes = addMes(ui.mes, -1); render(); };
  if (n) n.onclick = () => { ui.mes = addMes(ui.mes, 1); render(); };
}

/* ---------------- consultas ---------------- */
const cat = id => S.categorias.find(c => c.id === id) || {nome: 'Sem categoria', tipo: 'despesa', cor: '#c4c4c9', id: ''};
const conta = id => S.contas.find(c => c.id === id);
const pessoa = id => S.pessoas.find(p => p.id === id);
const nomePessoa = id => id === 'casal' ? 'Casal' : (pessoa(id)?.nome || '—');
const optPessoas = () => [...S.pessoas.map(p => [p.id, p.nome]), ...(S.pessoas.length > 1 ? [['casal', 'Casal (conjunto)']] : [])];
function donoLanc(l) { return l.dono || conta(l.conta)?.dono || 'casal'; }
function passaPessoa(dono) { return ui.pessoa === 'todos' || dono === ui.pessoa || dono === 'casal'; }
function lancsMes(m) { return S.lancamentos.filter(l => l.mesRef === m && passaPessoa(donoLanc(l))); }
function totaisMes(m) {
  const t = {rec: 0, desp: 0, res: 0, porCat: {}};
  for (const l of lancsMes(m)) {
    const c = cat(l.cat);
    if (c.tipo === 'neutro') continue;
    if (c.tipo === 'reserva') { t.res += -l.valor; continue; }
    if (l.valor > 0 && (c.tipo === 'receita' || !l.cat)) { t.rec += l.valor; continue; }
    if (l.valor < 0 && c.tipo === 'receita') { t.rec += l.valor; continue; }
    // despesas (estornos com sinal positivo em categoria de despesa abatem)
    t.desp += -l.valor; t.porCat[c.id] = (t.porCat[c.id] || 0) - l.valor;
  }
  return t;
}
function mediaDesp(m, n = 3) { let s = 0, k = 0; for (let i = 1; i <= n; i++) { const t = totaisMes(addMes(m, -i)); if (t.desp > 0) { s += t.desp; k++; } } return k ? s / k : 0; }
function sobraMedia(m, n = 3) { let s = 0, k = 0; for (let i = 1; i <= n; i++) { const t = totaisMes(addMes(m, -i)); if (t.desp > 0 || t.rec > 0) { s += t.rec - t.desp; k++; } } return k ? s / k : 0; }
function vencimentoFixa(f, m) { const [y, mm] = m.split('-').map(Number); const ult = new Date(y, mm, 0).getDate(); return m + '-' + String(Math.min(f.dia || 1, ult)).padStart(2, '0'); }
function fixasVisiveis(m) { m = m || ui.mes; return S.fixas.filter(f => f.ativa !== false && passaPessoa(f.dono || 'casal') && (!f.desde || f.desde <= m)); }
function saldoMeta(mt) { return (mt.saldo || 0) + S.investimentos.filter(i => i.meta === mt.id).reduce((s, i) => s + (i.atual || 0), 0); }
function aplicarRegras(desc) {
  const d = norm(desc);
  const rs = [...S.regras].sort((a, b) => b.termo.length - a.termo.length);
  for (const r of rs) if (r.termo && d.includes(norm(r.termo))) return r.cat;
  return '';
}
function parcelasFuturas(mBase) {
  // projeta parcelas restantes a partir das compras parceladas já lançadas
  const grupos = {};
  for (const l of S.lancamentos) {
    if (!l.parcela || !passaPessoa(donoLanc(l))) continue;
    const [x, y] = l.parcela.split('/').map(Number); if (!x || !y || x > y) continue;
    const base = norm(l.desc).replace(/\b\d{1,2}\/\d{1,2}\b/g, '').replace(/PARC(ELA)?/g, '').trim();
    const k = l.conta + '|' + base + '|' + Math.abs(l.valor).toFixed(2) + '|' + y;
    if (!grupos[k] || x > grupos[k].x) grupos[k] = {x, y, mes: l.mesRef, valor: -l.valor, desc: l.desc};
  }
  const porMes = {};
  for (const g of Object.values(grupos)) for (let i = 1; i <= g.y - g.x; i++) { const m = addMes(g.mes, i); if (m > mBase) porMes[m] = (porMes[m] || 0) + g.valor; }
  return porMes;
}

/* ---------------- modal / formulários ---------------- */
function fecharModal() { $('#modal').classList.add('hidden'); $('#modal').innerHTML = ''; if (renderPendente && S) { renderPendente = false; ordenarEstado(); render(); } }
function modal(html, {lg = false} = {}) {
  const m = $('#modal'); m.innerHTML = `<div class="box ${lg ? 'lg' : ''}">${html}</div>`; m.classList.remove('hidden');
  m.onclick = e => { if (e.target === m) fecharModal(); };
  return m.firstElementChild;
}
function campo(f, v) {
  const id = 'f_' + f.k; v = v ?? f.def ?? '';
  let inp;
  if (f.type === 'select') inp = `<select class="in" id="${id}">${(f.vazio ? `<option value="">${esc(f.vazio)}</option>` : '') + f.options.map(([a, b]) => `<option value="${esc(a)}" ${String(a) === String(v) ? 'selected' : ''}>${esc(b)}</option>`).join('')}</select>`;
  else if (f.type === 'textarea') inp = `<textarea class="in" id="${id}">${esc(v)}</textarea>`;
  else if (f.type === 'checkbox') return `<div class="fld"><label class="chk"><input type="checkbox" id="${id}" ${v ? 'checked' : ''}> ${esc(f.label)}</label>${f.help ? `<div class="help">${esc(f.help)}</div>` : ''}</div>`;
  else if (f.type === 'money') inp = `<input class="in" id="${id}" inputmode="decimal" value="${v === '' ? '' : esc(fmtN(+v, 2))}" placeholder="0,00">`;
  else inp = `<input class="in" id="${id}" type="${f.type || 'text'}" ${f.step ? `step="${f.step}"` : ''} ${f.min != null ? `min="${f.min}"` : ''} ${f.max != null ? `max="${f.max}"` : ''} value="${esc(v)}" ${f.ph ? `placeholder="${esc(f.ph)}"` : ''} autocomplete="off">`;
  return `<div class="fld"><label for="${id}">${esc(f.label)}</label>${inp}${f.help ? `<div class="help">${esc(f.help)}</div>` : ''}</div>`;
}
const CAMPO_PRIV = () => ({k: 'priv', label: '🔒 Privado — só eu vejo', type: 'checkbox', help: 'Cifrado com uma chave só sua. Os outros usuários não enxergam este item.'});
function formModal(titulo, campos, valores, aoSalvar, {aoExcluir, sub} = {}) {
  if (campos.some(f => f.k === 'priv')) { valores = {...valores, priv: !!valores.privado}; const orig = aoSalvar; aoSalvar = v => { v.privado = v.priv ? USER.uid : ''; delete v.priv; return orig(v); }; }
  const linhas = []; let buf = [];
  for (const f of campos) { if (f.half) { buf.push(f); if (buf.length === 2) { linhas.push(`<div class="frow">${buf.map(x => campo(x, valores[x.k])).join('')}</div>`); buf = []; } } else { if (buf.length) { linhas.push(`<div class="frow">${buf.map(x => campo(x, valores[x.k])).join('')}</div>`); buf = []; } linhas.push(campo(f, valores[f.k])); } }
  if (buf.length) linhas.push(`<div class="frow">${buf.map(x => campo(x, valores[x.k])).join('')}</div>`);
  const box = modal(`<h3>${esc(titulo)}</h3>${sub ? `<div class="small muted">${esc(sub)}</div>` : ''}<div class="filete"></div>${linhas.join('')}<div class="erro" id="ferr"></div>
    <div class="acts">${aoExcluir ? '<button class="btn esq" id="fdel" style="color:var(--vermelho)">Excluir</button>' : ''}<button class="btn" id="fcan">Cancelar</button><button class="btn pri" id="fok">Salvar</button></div>`);
  box.querySelector('#fcan').onclick = fecharModal;
  if (aoExcluir) box.querySelector('#fdel').onclick = () => { if (confirm('Excluir este item? Não dá para desfazer.')) { aoExcluir(); salvar(); fecharModal(); render(); } };
  box.querySelector('#fok').onclick = () => {
    const out = {};
    for (const f of campos) {
      const el = box.querySelector('#f_' + f.k);
      let v = f.type === 'checkbox' ? el.checked : el.value;
      if (f.type === 'money') v = parseBR(v);
      if (f.type === 'number') v = v === '' ? 0 : +v;
      if (f.req && (v === '' || v == null)) { box.querySelector('#ferr').textContent = `Preencha "${f.label}".`; return; }
      out[f.k] = v;
    }
    const r = aoSalvar(out); if (r === false) return;
    salvar(); fecharModal(); render();
  };
  const first = box.querySelector('input,select,textarea'); if (first) setTimeout(() => first.focus(), 30);
  return box;
}
const optCats = (tipos) => S.categorias.filter(c => !tipos || tipos.includes(c.tipo)).map(c => [c.id, c.nome]);
const optContas = (tipo) => S.contas.filter(c => !tipo || c.tipo === tipo).map(c => [c.id, c.nome + (S.pessoas.length > 1 ? ' · ' + nomePessoa(c.dono) : '')]);

/* =====================================================================
   PAINEL
   ===================================================================== */
function vPainel(el) {
  const m = ui.mes, t = totaisMes(m), med = mediaDesp(m);
  const saldo = t.rec - t.desp - t.res;
  el.innerHTML = topo(`Olá, ${esc(USER.nome)}`, {mes: true}) + `
  <div class="grid g4">
    <div class="card kpi"><div class="lb">Receitas</div><div class="v pos">${fmtR(t.rec)}</div><div class="s">entradas do mês</div></div>
    <div class="card kpi"><div class="lb">Despesas</div><div class="v neg">${fmtR(t.desp)}</div><div class="s">${med ? (t.desp > med ? '▲ ' : '▼ ') + fmtPct(Math.abs(t.desp / med - 1)) + ' vs. média 3 meses' : 'sem histórico ainda'}</div></div>
    <div class="card kpi"><div class="lb">Guardado</div><div class="v">${fmtR(t.res)}</div><div class="s">aportes em investimentos</div></div>
    <div class="card kpi dest"><div class="lb">Sobra do mês</div><div class="v ${saldo >= 0 ? 'pos' : 'neg'}">${fmtR(saldo)}</div><div class="s">receitas − despesas − aportes</div></div>
  </div>
  <div class="grid g2" style="margin-top:16px">
    <div class="card"><h3>Atenção <span class="x small muted" id="nalert"></span></h3><div id="alertas"></div></div>
    <div class="card"><h3>Onde o dinheiro foi <span class="x"><button class="btn sm" data-go="resumo">Ver resumo</button></span></h3>${barrasCategorias(t, 8)}</div>
  </div>
  <div class="grid g2" style="margin-top:16px">
    <div class="card"><h3>Últimos 6 meses</h3>${graficoMeses(m, 6)}</div>
    <div class="card"><h3>Reservas e metas <span class="x"><button class="btn sm" data-go="metas">Abrir</button></span></h3>${resumoMetas()}</div>
  </div>`;
  ligarTopo(el);
  el.querySelectorAll('[data-go]').forEach(b => b.onclick = () => { ui.view = b.dataset.go; render(); });
  const al = alertas(m);
  el.querySelector('#nalert').textContent = al.length ? al.length + ' item(ns)' : '';
  el.querySelector('#alertas').innerHTML = al.length ? al.map(a => `<div class="alert ${a.cls || ''}"><div class="tx"><b>${a.t}</b><span class="small muted">${a.s || ''}</span></div>${a.btn || ''}</div>`).join('') : '<div class="vazio">Tudo em dia por aqui.</div>';
  el.querySelectorAll('[data-wa]').forEach(b => b.onclick = () => abrirWhats(b.dataset.wa, m));
  el.querySelectorAll('[data-pagar]').forEach(b => b.onclick = () => pagarFixa(b.dataset.pagar, m));
  el.querySelectorAll('[data-acao="backup"]').forEach(b => b.onclick = exportarBackup);
}
function alertas(m) {
  const a = [], h = hoje();
  // backup
  const ub = S.config.ultimoBackup; const dias = ub ? diasEntre(ub.slice(0, 10), h) : null;
  if (dias == null || dias > 30) a.push({t: dias == null ? 'Nenhum backup exportado ainda' : `Último backup há ${dias} dias`, s: 'Os dados estão cifrados na nuvem, mas uma cópia extra é sempre bom ter.', cls: '', btn: '<button class="btn sm" data-acao="backup">Exportar</button>'});
  for (const it of S.config.pluggy?.itens || []) { if (!it.consentExpira) continue; const d = diasEntre(h, it.consentExpira.slice(0, 10)); if (d <= 30) a.push({t: `Autorização do ${esc(it.banco || 'banco')} ${d < 0 ? 'expirou' : 'expira em ' + d + ' dia(s)'}`, s: 'Renove no Meu Pluggy para continuar recebendo os lançamentos.', cls: d < 7 ? 'red' : 'warn'}); }
  if (S.config.pluggy?.geradoEm && diasEntre(S.config.pluggy.geradoEm.slice(0, 10), h) > 3) a.push({t: 'Sincronização com os bancos parada', s: 'Último pacote recebido em ' + fmtData(S.config.pluggy.geradoEm.slice(0, 10)) + '. Verifique o robô no GitHub.', cls: 'warn'});
  // contas fixas
  for (const f of fixasVisiveis(m)) {
    const pg = S.pagFixas[m]?.[f.id]; if (pg) continue;
    const v = vencimentoFixa(f, m), d = diasEntre(h, v);
    if (d <= 7) a.push({t: `${esc(f.nome)} — ${d < 0 ? 'vencida há ' + (-d) + ' dia(s)' : d === 0 ? 'vence hoje' : 'vence em ' + d + ' dia(s)'}`, s: `${fmtR(f.valor)} · dia ${f.dia}`, cls: d < 0 ? 'red' : d <= 2 ? 'warn' : '', btn: `<button class="btn sm" data-pagar="${f.id}">Marcar paga</button>`});
  }
  // filhos
  for (const fi of S.filhos) {
    const pend = pendenciasFilho(fi, m); if (!pend.length) continue;
    const dl = m + '-' + String(fi.dia || 1).padStart(2, '0');
    if (h >= dl || m < mesAtual()) a.push({t: `Cobrar ${esc(fi.nome)}: ${pend.length} conta(s) não enviada(s)`, s: pend.map(f => esc(f.nome)).join(', '), cls: 'warn', btn: `<button class="btn sm wa" data-wa="${fi.id}">WhatsApp</button>`});
  }
  // cartões
  for (const c of S.contas.filter(c => c.tipo === 'cartao' && passaPessoa(c.dono))) {
    if (!c.vencimento) continue;
    const v = vencimentoFixa({dia: c.vencimento}, m), d = diasEntre(h, v);
    const tot = -S.lancamentos.filter(l => l.conta === c.id && l.mesRef === m && cat(l.cat).tipo !== 'neutro').reduce((s, l) => s + l.valor, 0);
    if (d >= 0 && d <= 7 && tot > 0) a.push({t: `Fatura ${esc(c.nome)} vence em ${d} dia(s)`, s: `${fmtR(tot)} lançados nesta fatura`});
  }
  // milhas
  for (const p of S.milhas.filter(p => passaPessoa(p.dono || 'casal'))) {
    if (!p.vencimento || !p.aVencer) continue;
    const d = diasEntre(h, p.vencimento);
    if (d >= 0 && d <= 60) a.push({t: `${fmtN(p.aVencer)} pontos ${esc(p.programa)} vencem em ${d} dias`, s: fmtData(p.vencimento), cls: d <= 15 ? 'red' : 'warn'});
  }
  // orçamento
  const t = totaisMes(m);
  for (const c of S.categorias.filter(c => c.limite > 0)) { const g = t.porCat[c.id] || 0; if (g > c.limite) a.push({t: `${esc(c.nome)} passou do limite`, s: `${fmtR(g)} de ${fmtR(c.limite)}`, cls: 'red'}); }
  return a;
}
function barrasCategorias(t, max) {
  const arr = Object.entries(t.porCat).filter(([, v]) => v > 0.005).sort((a, b) => b[1] - a[1]);
  if (!arr.length) return '<div class="vazio">Nenhuma despesa neste mês. Importe uma fatura ou extrato.</div>';
  const top = arr.slice(0, max), resto = arr.slice(max).reduce((s, [, v]) => s + v, 0), mx = top[0][1];
  return top.map(([id, v]) => { const c = cat(id); const lim = c.limite > 0;
    return `<div class="catrow"><div class="n"><span class="dot" style="background:${c.cor}"></span>${esc(c.nome)}</div><div><div class="bar"><i class="${lim && v > c.limite ? 'red' : ''}" style="width:${Math.max(2, (lim ? Math.min(v / c.limite, 1) : v / mx) * 100)}%;${!lim ? 'background:' + c.cor : ''}"></i></div>${lim ? `<div class="lim">limite ${fmtR(c.limite)}</div>` : ''}</div><div class="val">${fmtR(v)}<div class="lim">${fmtPct(v / t.desp)}</div></div></div>`; }).join('')
    + (resto > 0 ? `<div class="catrow"><div class="n muted">Demais categorias</div><div></div><div class="val muted">${fmtR(resto)}</div></div>` : '');
}
function graficoMeses(m, n) {
  const ms = []; for (let i = n - 1; i >= 0; i--) ms.push(addMes(m, -i));
  const d = ms.map(x => totaisMes(x)); const mx = Math.max(1, ...d.map(x => Math.max(x.rec, x.desp)));
  const W = 520, H = 200, pad = 28, bw = (W - pad) / n;
  let s = `<svg viewBox="0 0 ${W} ${H + 30}" width="100%" role="img" aria-label="Receitas e despesas por mês">`;
  for (let g = 0; g <= 4; g++) { const y = H - (H - 10) * g / 4; s += `<line x1="${pad}" x2="${W}" y1="${y}" y2="${y}" stroke="#ececee"/><text x="${pad - 4}" y="${y + 3}" font-size="9" text-anchor="end" fill="#8a8a93">${fmtN(mx * g / 4 / 1000, 0)}k</text>`; }
  d.forEach((x, i) => {
    const x0 = pad + i * bw + bw * 0.18, w = bw * 0.3;
    const hr = Math.max(0, (H - 10) * x.rec / mx), hd = Math.max(0, (H - 10) * x.desp / mx);
    s += `<rect x="${x0}" y="${H - hr}" width="${w}" height="${hr}" rx="3" fill="#1f8a4c"><title>Receitas ${fmtR(x.rec)}</title></rect>`;
    s += `<rect x="${x0 + w + 3}" y="${H - hd}" width="${w}" height="${hd}" rx="3" fill="${ms[i] === m ? '#d0232b' : '#141414'}"><title>Despesas ${fmtR(x.desp)}</title></rect>`;
    s += `<text x="${x0 + w}" y="${H + 16}" font-size="11" text-anchor="middle" fill="${ms[i] === m ? '#141414' : '#8a8a93'}" ${ms[i] === m ? 'font-weight="700"' : ''}>${nomeMesCurto(ms[i])}</text>`;
  });
  return s + `</svg><div class="legend"><span><span class="dot" style="background:#1f8a4c"></span>Receitas</span><span><span class="dot" style="background:#141414"></span>Despesas</span><span><span class="dot" style="background:#d0232b"></span>Mês selecionado</span></div>`;
}
function resumoMetas() {
  const ms = S.metas.filter(x => passaPessoa(x.dono || 'casal'));
  if (!ms.length) return '<div class="vazio">Crie metas para viagem, aposentadoria e reserva de emergência.</div>';
  return '<div class="list">' + ms.map(mt => { const sd = saldoMeta(mt), p = mt.alvo ? sd / mt.alvo : 0, ap = aporteNecessario(mt);
    return `<div class="it"><div class="grow"><b>${esc(mt.nome)}</b> <span class="tag">${esc(TIPO_META[mt.tipo] || mt.tipo)}</span><div class="bar" style="margin:6px 0 2px"><i class="${p >= 1 ? 'ok' : ''}" style="width:${Math.min(100, p * 100)}%"></i></div><span class="small muted">${fmtR(sd)} de ${fmtR(mt.alvo)} · ${fmtPct(p)}${ap > 0 ? ' · guardar ' + fmtR(ap) + '/mês' : ''}</span></div></div>`; }).join('') + '</div>';
}

/* =====================================================================
   RESUMO MENSAL
   ===================================================================== */
function vResumo(el) {
  const m = ui.mes, t = totaisMes(m), ls = lancsMes(m);
  const cats = Object.entries(t.porCat).filter(([, v]) => Math.abs(v) > 0.005).sort((a, b) => b[1] - a[1]);
  const medCat = id => { let s = 0, k = 0; for (let i = 1; i <= 3; i++) { const tt = totaisMes(addMes(m, -i)); if (tt.desp > 0) { s += tt.porCat[id] || 0; k++; } } return k ? s / k : null; };
  const desp = ls.filter(l => l.valor < 0 && ['despesa'].includes(cat(l.cat).tipo)).sort((a, b) => a.valor - b.valor);
  // estabelecimentos frequentes
  const est = {}; for (const l of desp) { const k = norm(l.desc).replace(/\b\d{1,2}\/\d{1,2}\b/g, '').replace(/\s+\d+$/, '').slice(0, 26).trim(); est[k] = est[k] || {n: 0, v: 0, d: l.desc}; est[k].n++; est[k].v += -l.valor; }
  const freq = Object.values(est).filter(x => x.n >= 2).sort((a, b) => b.v - a.v).slice(0, 8);
  // por conta
  const pc = {}; for (const l of desp) pc[l.conta || '-'] = (pc[l.conta || '-'] || 0) - l.valor;
  // fixas
  const fx = fixasVisiveis(); const fixPrev = fx.reduce((s, f) => s + (f.valor || 0), 0);
  const fixPago = fx.reduce((s, f) => s + (S.pagFixas[m]?.[f.id]?.valor || 0), 0);
  const parc = parcelasFuturas(m); const parcMes = ls.filter(l => l.parcela && l.valor < 0).reduce((s, l) => s - l.valor, 0);
  const subiram = cats.map(([id, v]) => ({id, v, md: medCat(id)})).filter(x => x.md != null && x.md > 0 && x.v - x.md > 50).sort((a, b) => (b.v - b.md) - (a.v - a.md)).slice(0, 4);
  el.innerHTML = topo('Resumo mensal', {mes: true, extra: '<button class="btn noprint" id="bprint">Imprimir / PDF</button>'}) + `
  <div class="grid g4">
    <div class="card kpi"><div class="lb">Receitas</div><div class="v pos">${fmtR(t.rec)}</div></div>
    <div class="card kpi"><div class="lb">Despesas</div><div class="v neg">${fmtR(t.desp)}</div><div class="s">${ls.length} lançamentos</div></div>
    <div class="card kpi"><div class="lb">Parcelas no mês</div><div class="v">${fmtR(parcMes)}</div><div class="s">${t.desp ? fmtPct(parcMes / t.desp) + ' das despesas' : ''}</div></div>
    <div class="card kpi dest"><div class="lb">Sobra</div><div class="v ${t.rec - t.desp - t.res >= 0 ? 'pos' : 'neg'}">${fmtR(t.rec - t.desp - t.res)}</div><div class="s">guardado: ${fmtR(t.res)}</div></div>
  </div>
  ${subiram.length ? `<div class="card" style="margin-top:16px"><h3>O que mais pesou acima do normal</h3>${subiram.map(x => `<div class="alert warn"><div class="tx"><b>${esc(cat(x.id).nome)}: ${fmtR(x.v)}</b><span class="small muted">média dos 3 meses anteriores: ${fmtR(x.md)} → ${fmtR(x.v - x.md)} a mais (${fmtPct(x.v / x.md - 1)})</span></div></div>`).join('')}</div>` : ''}
  <div class="card" style="margin-top:16px"><h3>Despesas por categoria</h3>
    ${cats.length ? `<div class="tw"><table class="t"><thead><tr><th>Categoria</th><th class="r">Valor</th><th class="r">% do total</th><th class="r">Média 3 meses</th><th class="r">Variação</th><th class="r">Limite</th></tr></thead><tbody>
    ${cats.map(([id, v]) => { const c = cat(id), md = medCat(id); const vr = md ? v / md - 1 : null;
      return `<tr><td><span class="dot" style="background:${c.cor}"></span>${esc(c.nome)}</td><td class="r"><b>${fmtR(v)}</b></td><td class="r">${fmtPct(v / t.desp)}</td><td class="r">${md != null ? fmtR(md) : '·'}</td><td class="r ${vr > 0.1 ? 'neg' : vr < -0.1 ? 'pos' : ''}">${vr == null ? '·' : (vr > 0 ? '+' : '') + fmtPct(vr)}</td><td class="r">${c.limite ? `<span class="tag ${v > c.limite ? 'red' : 'ok'}">${fmtR(c.limite)}</span>` : '·'}</td></tr>`; }).join('')}
    <tr class="tot"><td>Total</td><td class="r">${fmtR(t.desp)}</td><td class="r">100%</td><td class="r">${fmtR(mediaDesp(m))}</td><td></td><td></td></tr></tbody></table></div>` : '<div class="vazio">Sem despesas neste mês.</div>'}
  </div>
  <div class="grid g2" style="margin-top:16px">
    <div class="card"><h3>10 maiores gastos</h3>${desp.length ? `<table class="t"><tbody>${desp.slice(0, 10).map(l => `<tr><td class="small">${fmtData(l.data)}</td><td>${esc(l.desc)}${l.parcela ? ` <span class="tag">${l.parcela}</span>` : ''}<div class="small muted">${esc(cat(l.cat).nome)} · ${esc(conta(l.conta)?.nome || '')}</div></td><td class="r"><b>${fmtR(-l.valor)}</b></td></tr>`).join('')}</tbody></table>` : '<div class="vazio">—</div>'}</div>
    <div class="card"><h3>Onde você compra com frequência</h3>${freq.length ? `<table class="t"><tbody>${freq.map(f => `<tr><td>${esc(f.d)}</td><td class="r small muted">${f.n}×</td><td class="r"><b>${fmtR(f.v)}</b></td></tr>`).join('')}</tbody></table>` : '<div class="vazio">Sem recorrências no mês.</div>'}</div>
  </div>
  <div class="grid g3" style="margin-top:16px">
    <div class="card"><h3>Por cartão / conta</h3>${Object.keys(pc).length ? '<div class="list">' + Object.entries(pc).sort((a, b) => b[1] - a[1]).map(([id, v]) => `<div class="it"><div class="grow">${esc(conta(id)?.nome || 'Sem conta')}<div class="small muted">${esc(conta(id) ? nomePessoa(conta(id).dono) : '')}</div></div><b>${fmtR(v)}</b></div>`).join('') + '</div>' : '<div class="vazio">—</div>'}</div>
    <div class="card"><h3>Contas fixas</h3><div class="list"><div class="it"><div class="grow">Previsto no mês</div><b>${fmtR(fixPrev)}</b></div><div class="it"><div class="grow">Já pago</div><b class="pos">${fmtR(fixPago)}</b></div><div class="it"><div class="grow">Fixas sobre as despesas</div><b>${t.desp ? fmtPct(fixPrev / t.desp) : '·'}</b></div></div></div>
    <div class="card"><h3>Parcelas já comprometidas</h3>${Object.keys(parc).length ? '<div class="list">' + Object.entries(parc).sort().slice(0, 6).map(([mm, v]) => `<div class="it"><div class="grow" style="text-transform:capitalize">${nomeMes(mm)}</div><b>${fmtR(v)}</b></div>`).join('') + '</div>' : '<div class="vazio">Nenhuma parcela futura identificada.</div>'}</div>
  </div>`;
  ligarTopo(el); el.querySelector('#bprint').onclick = () => print();
}

/* =====================================================================
   LANÇAMENTOS
   ===================================================================== */
function vLanc(el) {
  const f = ui.filtro;
  let ls = S.lancamentos.filter(l => l.mesRef === ui.mes && passaPessoa(donoLanc(l)));
  if (f.conta) ls = ls.filter(l => l.conta === f.conta);
  if (f.cat) ls = ls.filter(l => (f.cat === '_sem' ? !l.cat : l.cat === f.cat));
  if (f.q) { const q = norm(f.q); ls = ls.filter(l => norm(l.desc).includes(q)); }
  ls.sort((a, b) => b.data.localeCompare(a.data) || a.desc.localeCompare(b.desc));
  const tot = ls.reduce((s, l) => s + l.valor, 0);
  el.innerHTML = topo('Lançamentos', {mes: true, extra: '<button class="btn pri" id="bnovo">+ Novo lançamento</button>'}) + `
  <div class="card">
    <div class="ctrl" style="margin-bottom:12px">
      <input class="in" id="fq" placeholder="Buscar descrição…" value="${esc(f.q || '')}" style="max-width:240px">
      <select class="in" id="fconta" style="max-width:220px"><option value="">Todas as contas</option>${optContas().map(([a, b]) => `<option value="${a}" ${f.conta === a ? 'selected' : ''}>${esc(b)}</option>`).join('')}</select>
      <select class="in" id="fcat" style="max-width:220px"><option value="">Todas as categorias</option><option value="_sem" ${f.cat === '_sem' ? 'selected' : ''}>— Sem categoria —</option>${optCats().map(([a, b]) => `<option value="${a}" ${f.cat === a ? 'selected' : ''}>${esc(b)}</option>`).join('')}</select>
      <span class="muted small" style="margin-left:auto">${ls.length} itens · saldo ${fmtR(tot)}</span>
    </div>
    <div class="small muted" style="margin-bottom:8px">Para cartões, o mês é o da <b>fatura</b> (competência). Trocar a categoria aqui pode criar uma regra para as próximas importações.</div>
    ${ls.length ? `<div class="tw"><table class="t"><thead><tr><th>Data</th><th>Descrição</th><th>Categoria</th><th>Conta</th>${S.pessoas.length > 1 ? '<th>Lançado por</th>' : ''}<th class="r">Valor</th><th></th></tr></thead><tbody>
    ${ls.map(l => `<tr><td class="small">${fmtData(l.data)}</td><td>${esc(l.desc)}${l.privado ? ' <span class="lock" title="Privado">🔒</span>' : ''}${l.origem === 'banco' ? ' <span class="tag" title="Veio do banco (Open Finance)">banco</span>' : ''}${l.parcela ? ` <span class="tag">${l.parcela}</span>` : ''}${l.obs ? `<div class="small muted">${esc(l.obs)}</div>` : ''}</td>
      <td><select data-cat="${l.id}"><option value="">— escolher —</option>${S.categorias.map(c => `<option value="${c.id}" ${l.cat === c.id ? 'selected' : ''}>${esc(c.nome)}</option>`).join('')}</select></td>
      <td class="small">${esc(conta(l.conta)?.nome || '')}</td>${S.pessoas.length > 1 ? `<td class="small muted">${esc(l.autor || '')}</td>` : ''}
      <td class="r ${l.valor < 0 ? '' : 'pos'}"><b>${fmtR(l.valor)}</b></td><td class="r"><button class="btn sm ghost" data-ed="${l.id}">Editar</button></td></tr>`).join('')}
    </tbody></table></div>` : '<div class="vazio">Nenhum lançamento neste mês com esses filtros.</div>'}
  </div>`;
  ligarTopo(el);
  el.querySelector('#bnovo').onclick = () => editarLanc();
  const re = () => render();
  el.querySelector('#fq').oninput = e => { f.q = e.target.value; clearTimeout(vLanc._t); vLanc._t = setTimeout(() => { re(); const i = $('#fq'); i.focus(); i.setSelectionRange(i.value.length, i.value.length); }, 350); };
  el.querySelector('#fconta').onchange = e => { f.conta = e.target.value; re(); };
  el.querySelector('#fcat').onchange = e => { f.cat = e.target.value; re(); };
  el.querySelectorAll('[data-ed]').forEach(b => b.onclick = () => editarLanc(S.lancamentos.find(l => l.id === b.dataset.ed)));
  el.querySelectorAll('[data-cat]').forEach(s => s.onchange = () => {
    const l = S.lancamentos.find(x => x.id === s.dataset.cat); l.cat = s.value; salvar();
    if (s.value) perguntarRegra(l.desc, s.value);
  });
}
function perguntarRegra(desc, catId) {
  const sug = norm(desc).replace(/\b\d{1,2}\/\d{1,2}\b/g, '').replace(/[*]/g, ' ').replace(/\s\d+$/, '').trim().split(' ').slice(0, 2).join(' ');
  if (!sug || S.regras.some(r => norm(r.termo) === sug && r.cat === catId)) return;
  const box = modal(`<h3>Criar regra?</h3><div class="filete"></div><p>Sempre que a descrição contiver o termo abaixo, classificar como <b>${esc(cat(catId).nome)}</b>.</p>
    <div class="fld"><label>Termo</label><input class="in" id="rt" value="${esc(sug)}"></div>
    <label class="chk"><input type="checkbox" id="rap" checked> Aplicar também aos lançamentos já existentes sem categoria</label>
    <div class="acts"><button class="btn" id="rn">Não</button><button class="btn pri" id="rs">Criar regra</button></div>`);
  box.querySelector('#rn').onclick = fecharModal;
  box.querySelector('#rs').onclick = () => {
    const termo = box.querySelector('#rt').value.trim(); if (!termo) return fecharModal();
    S.regras = S.regras.filter(r => norm(r.termo) !== norm(termo)); S.regras.push({id: uid(), termo, cat: catId});
    let n = 0; if (box.querySelector('#rap').checked) for (const l of S.lancamentos) if (!l.cat && norm(l.desc).includes(norm(termo))) { l.cat = catId; n++; }
    salvar(); fecharModal(); toast('Regra criada' + (n ? ` · ${n} lançamento(s) classificados` : '')); render();
  };
}
function editarLanc(l) {
  const novo = !l; l = l || {data: hoje(), mesRef: ui.mes, valor: 0, desc: '', cat: '', conta: S.contas[0]?.id || ''};
  const tipoIni = l.valor > 0 ? 'entrada' : 'saida';
  formModal(novo ? 'Novo lançamento' : 'Editar lançamento', [
    {k: 'desc', label: 'Descrição', req: true},
    {k: 'tipo', label: 'Tipo', type: 'select', options: [['saida', 'Saída / despesa'], ['entrada', 'Entrada / receita']], half: true},
    {k: 'valor', label: 'Valor (R$)', type: 'money', req: true, half: true},
    {k: 'data', label: 'Data', type: 'date', req: true, half: true},
    {k: 'mesRef', label: 'Mês de competência', type: 'month', req: true, half: true, help: 'Para cartão: mês da fatura.'},
    {k: 'cat', label: 'Categoria', type: 'select', options: optCats(), vazio: '— sem categoria —', half: true},
    {k: 'conta', label: 'Conta / cartão', type: 'select', options: optContas(), vazio: '— nenhuma —', half: true},
    {k: 'parcela', label: 'Parcela (ex.: 3/10)', half: true},
    ...(S.pessoas.length > 1 ? [{k: 'dono', label: 'De quem é o gasto', type: 'select', options: optPessoas(), vazio: '(segue o dono da conta)', half: true}] : []),
    {k: 'obs', label: 'Observação'},
    CAMPO_PRIV(),
  ], {...l, tipo: tipoIni, valor: Math.abs(l.valor) || ''}, v => {
    const val = Math.abs(v.valor) * (v.tipo === 'saida' ? -1 : 1);
    const o = {...l, desc: v.desc, valor: val, data: v.data, mesRef: v.mesRef, cat: v.cat, conta: v.conta, parcela: v.parcela.trim(), obs: v.obs, dono: v.dono || '', privado: v.privado};
    if (novo) { o.id = uid(); o.origem = 'manual'; o.autor = USER.nome; S.lancamentos.push(o); } else Object.assign(l, o);
  }, {aoExcluir: novo ? null : () => { S.lancamentos = S.lancamentos.filter(x => x.id !== l.id); }});
}

/* =====================================================================
   IMPORTAÇÃO (PDF / OFX / CSV)
   ===================================================================== */
let pdfPronto = null;
function iniciarPdf() {
  if (!pdfPronto) pdfPronto = new Promise((ok, falha) => { const s = document.createElement('script'); s.src = 'vendor/pdf.min.js'; s.onload = () => { pdfjsLib.GlobalWorkerOptions.workerSrc = 'vendor/pdf.worker.min.js'; ok(); }; s.onerror = () => { pdfPronto = null; falha(new Error('não consegui carregar o leitor de PDF')); }; document.head.appendChild(s); });
  return pdfPronto;
}
function pedirSenhaPdf(motivo) {
  return new Promise(res => {
    const box = modal(`<h3>PDF protegido por senha</h3><div class="filete"></div><p class="small">${motivo === 2 ? 'Senha incorreta. Tente novamente.' : 'Muitos bancos protegem a fatura com parte do CPF. A senha é usada só para abrir o arquivo e não é guardada.'}</p>
      <div class="fld"><label>Senha do PDF</label><input class="in" id="pp" type="password" autocomplete="off"></div>
      <div class="acts"><button class="btn" id="pc">Cancelar</button><button class="btn pri" id="po">Abrir</button></div>`);
    const ok = () => { const v = box.querySelector('#pp').value; fecharModal(); res(v); };
    box.querySelector('#po').onclick = ok; box.querySelector('#pp').onkeydown = e => { if (e.key === 'Enter') ok(); };
    box.querySelector('#pc').onclick = () => { fecharModal(); res(null); };
    setTimeout(() => box.querySelector('#pp').focus(), 30);
  });
}
async function textoPdf(buf) {
  await iniciarPdf();
  const task = pdfjsLib.getDocument({data: buf, isEvalSupported: false, disableFontFace: true, useSystemFonts: false});
  task.onPassword = async (upd, motivo) => { const s = await pedirSenhaPdf(motivo); if (s == null) task.destroy(); else upd(s); };
  const doc = await task.promise; const paginas = [];
  for (let p = 1; p <= doc.numPages; p++) {
    const pg = await doc.getPage(p); const tc = await pg.getTextContent(); const vw = pg.getViewport({scale: 1});
    const itens = tc.items.filter(i => i.str && i.str.trim()).map(i => ({s: i.str, x: i.transform[4], y: i.transform[5], w: i.width, h: Math.abs(i.transform[3]) || 8}));
    // separa colunas (faturas com 2 colunas, ex. Itaú): se houver muitas linhas de data começando na metade direita
    const linhas = agruparLinhas(itens, vw.width);
    paginas.push(linhas);
  }
  await doc.destroy();
  return paginas;
}
function agruparLinhas(itens, largura) {
  const reData = /^(\d{2}\/\d{2}(\/\d{2,4})?|\d{2}\s?(JAN|FEV|MAR|ABR|MAI|JUN|JUL|AGO|SET|OUT|NOV|DEZ))/i;
  const meio = largura / 2;
  const dir = itens.filter(i => i.x > meio - 5 && reData.test(i.s.trim())).length, esq = itens.filter(i => i.x < meio - 5 && reData.test(i.s.trim())).length;
  const duasColunas = dir >= 4 && esq >= 4;
  const grupos = duasColunas ? [itens.filter(i => i.x < meio - 5), itens.filter(i => i.x >= meio - 5)] : [itens];
  const out = [];
  for (const g of grupos) {
    const ord = [...g].sort((a, b) => b.y - a.y || a.x - b.x); const ls = [];
    for (const it of ord) { const l = ls.find(l => Math.abs(l.y - it.y) < Math.max(2.5, it.h * 0.35)); if (l) l.its.push(it); else ls.push({y: it.y, its: [it]}); }
    ls.sort((a, b) => b.y - a.y);
    for (const l of ls) { l.its.sort((a, b) => a.x - b.x); let s = '', fim = null; for (const it of l.its) { if (fim != null) { const gap = it.x - fim; s += gap > 12 ? '   ' : gap > 1.5 ? ' ' : ''; } s += it.s; fim = it.x + it.w; } out.push(s.replace(/\s+$/, '')); }
  }
  return out;
}
const RE_VAL = '(-\\s?)?(?:R\\$\\s?)?(-\\s?)?(\\d{1,3}(?:\\.\\d{3})*,\\d{2})(\\s?[-DC](?![A-Za-z]))?';
const RE_DATA = '(\\d{2}\\/\\d{2}(?:\\/\\d{2,4})?|\\d{2}\\s?(?:JAN|FEV|MAR|ABR|MAI|JUN|JUL|AGO|SET|OUT|NOV|DEZ)[A-Z]*\\.?)';
const IGNORAR = /(SALDO ANTERIOR|SALDO DO DIA|SALDO FINAL|SALDO DISPON|SALDO EM C|TOTAL DA FATURA|TOTAL DESTA FATURA|TOTAL DE |TOTAL GERAL|SUBTOTAL|LIMITE |PAGAMENTO MINIMO|PAGAMENTO MÍNIMO|VALOR MINIMO|VENCIMENTO|^TOTAL\b|SALDO\s*$|S A L D O|LANCAMENTOS NO CARTAO|ENCARGOS PARA O PROXIMO|PROXIMA FATURA|CET\b|TAXA DE JUROS|JUROS DO ROTATIVO|EQUIVALENTE)/i;
const SAIDA_KW = /(PIX ENVIADO|PIX TRANSF|PIX - ENV|TRANSF ENVIADA|TED ENVIADA|DOC ENVIADO|PAGTO|PAGAMENTO|PAG\b|COMPRA|SAQUE|DEBITO|DÉBITO|TARIFA|IOF|BOLETO|APLICACAO|APLIC\b|CARTAO|ENVIADO)/i;
const ENTRADA_KW = /(PIX RECEBIDO|PIX - REC|RECEBID|TED RECEBIDA|TRANSF RECEBIDA|CREDITO|CRÉDITO|SALARIO|SALÁRIO|DEPOSITO|DEPÓSITO|RESGATE|RENDIMENTO|ESTORNO|DEVOLUCAO|REEMBOLSO|PROVENTO|DIVIDENDO)/i;
function dataPara(dStr, refMes, modo) {
  dStr = dStr.toUpperCase().replace(/\./g, '').replace(/\s+/g, ' ').trim();
  let dd, mm, yy = null;
  const m1 = dStr.match(/^(\d{2})\/(\d{2})(?:\/(\d{2,4}))?$/);
  if (m1) { dd = +m1[1]; mm = +m1[2]; if (m1[3]) yy = m1[3].length === 2 ? 2000 + +m1[3] : +m1[3]; }
  else { const m2 = dStr.match(/^(\d{2})\s?([A-Z]{3})/); if (!m2) return null; dd = +m2[1]; mm = MESES_AB.indexOf(m2[2]) + 1; if (!mm) return null; }
  if (dd < 1 || dd > 31 || mm < 1 || mm > 12) return null;
  if (!yy) { const [ry, rm] = refMes.split('-').map(Number); yy = ry; if (mm > rm + (modo === 'extrato' ? 0 : 0)) yy = ry - 1; if (modo === 'extrato' && mm > rm) yy = ry - 1; }
  return yy + '-' + String(mm).padStart(2, '0') + '-' + String(dd).padStart(2, '0');
}
function lerLinhas(linhas, modo, refMes) {
  const re = new RegExp(RE_DATA + '\\s+(.+?)\\s+' + RE_VAL + '(?=\\s|$)', 'gi');
  const reSemData = new RegExp('^\\s*([A-Za-zÀ-ú*].+?)\\s+' + RE_VAL + '(?=\\s|$)', 'i');
  const out = []; let ultimaData = null; let totalLido = null;
  for (const linha of linhas) {
    const L = linha.replace(/[−–]/g, '-').replace(/ /g, ' ');
    const tm = L.match(/TOTAL (?:DA |DESTA )?FATURA[^\d]*?(\d{1,3}(?:\.\d{3})*,\d{2})/i) || L.match(/VALOR TOTAL[^\d]*?(\d{1,3}(?:\.\d{3})*,\d{2})/i);
    if (tm && totalLido == null) totalLido = parseBR(tm[1]);
    let achou = false; re.lastIndex = 0; let m;
    while ((m = re.exec(L))) {
      const data = dataPara(m[1], refMes, modo); if (!data) continue;
      const desc = m[2].replace(/\s{2,}/g, ' ').trim();
      if (IGNORAR.test(desc) || desc.length < 2) { ultimaData = data; achou = true; continue; }
      out.push(montarItem(data, desc, m[3], m[4], m[5], m[6], modo)); ultimaData = data; achou = true;
    }
    if (!achou && modo === 'extrato' && ultimaData) {
      const s = L.match(reSemData);
      if (s && !IGNORAR.test(s[1]) && s[1].length > 2) out.push(montarItem(ultimaData, s[1].replace(/\s{2,}/g, ' ').trim(), s[2], s[3], s[4], s[5], modo, true));
    }
  }
  return {itens: out, totalLido};
}
function montarItem(data, desc, n1, n2, num, suf, modo, semData) {
  let v = parseBR(num); const negTxt = !!(n1 || n2 || (suf && /-|D/i.test(suf))); const cred = !!(suf && /C/i.test(suf));
  let valor;
  if (modo === 'fatura') valor = negTxt || /ESTORNO|PAGAMENTO|CREDITO|CRÉDITO|DEVOLU/i.test(desc) ? v : -v;
  else { if (negTxt) valor = -v; else if (cred) valor = v; else if (ENTRADA_KW.test(desc)) valor = v; else if (SAIDA_KW.test(desc)) valor = -v; else valor = -v; }
  const pm = desc.match(/(?:PARC(?:ELA)?\.?\s*)?\b(\d{1,2})\s?\/\s?(\d{1,2})\b(?!\/)/i);
  let parcela = ''; if (pm && +pm[1] >= 1 && +pm[2] >= 2 && +pm[2] <= 48 && +pm[1] <= +pm[2]) parcela = (+pm[1]) + '/' + (+pm[2]);
  return {data, desc, valor, parcela, incerto: modo === 'extrato' && !negTxt && !cred, semData: !!semData};
}
function lerOFX(txt, modo) {
  const out = [];
  const blocos = txt.split(/<STMTTRN>/i).slice(1);
  const tag = (b, t) => { const m = b.match(new RegExp('<' + t + '>([^<\\r\\n]*)', 'i')); return m ? m[1].trim() : ''; };
  for (const b of blocos) {
    const d = tag(b, 'DTPOSTED'); if (!d) continue;
    const data = d.slice(0, 4) + '-' + d.slice(4, 6) + '-' + d.slice(6, 8);
    let valor = parseFloat(tag(b, 'TRNAMT').replace(',', '.')) || 0;
    const desc = (tag(b, 'MEMO') || tag(b, 'NAME') || tag(b, 'TRNTYPE')).replace(/\s{2,}/g, ' ');
    const pm = desc.match(/\b(\d{1,2})\/(\d{1,2})\b/); let parcela = ''; if (pm && +pm[2] >= 2 && +pm[1] <= +pm[2] && +pm[2] <= 48) parcela = (+pm[1]) + '/' + (+pm[2]);
    out.push({data, desc, valor, parcela, fitid: tag(b, 'FITID')});
  }
  return out;
}
function lerCSV(txt, modo) {
  const linhas = txt.replace(/^﻿/, '').split(/\r?\n/).filter(l => l.trim());
  if (linhas.length < 2) return [];
  const sep = (linhas[0].match(/;/g) || []).length > (linhas[0].match(/,/g) || []).length ? ';' : ',';
  const split = l => { const r = []; let cur = '', q = false; for (const ch of l) { if (ch === '"') q = !q; else if (ch === sep && !q) { r.push(cur); cur = ''; } else cur += ch; } r.push(cur); return r.map(x => x.trim()); };
  const cab = split(linhas[0]).map(norm);
  const idx = re => cab.findIndex(c => re.test(c));
  let iD = idx(/^DATA|^DATE/), iV = idx(/VALOR|AMOUNT|QUANTIA/), iT = idx(/DESCRI|TITLE|HISTORICO|ESTABELEC|LANCAMENTO/);
  const out = [];
  for (const l of linhas.slice(1)) {
    const c = split(l); if (iD < 0 || iV < 0) continue;
    let d = c[iD]; let data = null;
    if (/^\d{4}-\d{2}-\d{2}/.test(d)) data = d.slice(0, 10); else { const m = d.match(/^(\d{2})\/(\d{2})\/(\d{2,4})/); if (m) data = (m[3].length === 2 ? '20' + m[3] : m[3]) + '-' + m[2] + '-' + m[1]; }
    if (!data) continue;
    let vs = c[iV]; let v = /,\d{2}$/.test(vs) || vs.includes(',') && sep === ';' ? parseBR(vs) : parseFloat(vs);
    if (isNaN(v)) continue;
    const desc = iT >= 0 ? c[iT] : c.filter((x, i) => i !== iD && i !== iV).sort((a, b) => b.length - a.length)[0];
    if (modo === 'fatura') v = -v; // CSV de cartão (ex. Nubank): positivo = compra
    const pm = (desc || '').match(/\b(\d{1,2})\/(\d{1,2})\b/); let parcela = ''; if (pm && +pm[2] >= 2 && +pm[1] <= +pm[2] && +pm[2] <= 48) parcela = (+pm[1]) + '/' + (+pm[2]);
    out.push({data, desc: desc || '', valor: v, parcela});
  }
  return out;
}
const chaveDup = (contaId, l) => contaId + '|' + l.data + '|' + Math.abs(l.valor).toFixed(2) + '|' + norm(l.desc).slice(0, 18);

let IMP = null; // estado da importação em andamento
function vImportar(el) {
  if (IMP && IMP.itens) return vRevisao(el);
  const cartoes = optContas('cartao'), bancos = optContas('banco');
  el.innerHTML = topo('Importar faturas e extratos', {pessoa: false}) + `
  <div class="grid g2">
    <div class="card">
      <h3>1. O que você vai importar</h3>
      <div class="fld"><label>Tipo de documento</label><div class="seg" id="segtipo"><button data-t="fatura" class="on">Fatura de cartão</button><button data-t="extrato">Extrato bancário</button></div></div>
      <div class="fld"><label>Cartão / conta de destino</label><select class="in" id="imconta"></select><div class="help" id="hconta"></div></div>
      <div class="fld" id="fref"><label>Mês da fatura (competência)</label><input class="in" type="month" id="imref" value="${mesAtual()}"><div class="help">É o mês em que a fatura vence. Todos os itens dela entram neste mês.</div></div>
      <h3 style="margin-top:18px">2. Arquivo</h3>
      <div class="drop" id="drop"><b>Clique para escolher</b> ou arraste aqui<br><span class="small muted">PDF da fatura/extrato, OFX ou CSV</span></div>
      <input type="file" id="imfile" accept=".pdf,.ofx,.qfx,.csv,.txt" class="hidden">
      <div class="erro" id="imerr"></div>
    </div>
    <div class="card">
      <h3>Como funciona</h3>
      <div class="list small">
        <div class="it"><div class="grow"><b>Tudo é lido aqui mesmo.</b> O arquivo não sai do seu computador; nada é enviado para a internet.</div></div>
        <div class="it"><div class="grow"><b>Você confere antes de gravar.</b> Aparece uma tabela de revisão para marcar/desmarcar itens, ajustar categoria e sinal.</div></div>
        <div class="it"><div class="grow"><b>Duplicados são detectados.</b> Se você importar a mesma fatura duas vezes, os itens repetidos vêm desmarcados.</div></div>
        <div class="it"><div class="grow"><b>OFX é o formato mais confiável</b> para extratos (Itaú, Bradesco, BB, Caixa e XP exportam OFX no internet banking). O PDF funciona, mas cada banco tem um layout.</div></div>
        <div class="it"><div class="grow"><b>Categorias aprendem.</b> Ao corrigir uma categoria, você pode criar uma regra que vale para as próximas importações.</div></div>
      </div>
    </div>
  </div>`;
  let tipo = 'fatura';
  const atual = () => {
    el.querySelectorAll('#segtipo button').forEach(b => b.classList.toggle('on', b.dataset.t === tipo));
    const opts = tipo === 'fatura' ? cartoes : bancos;
    el.querySelector('#imconta').innerHTML = opts.map(([a, b]) => `<option value="${a}">${esc(b)}</option>`).join('');
    el.querySelector('#hconta').innerHTML = opts.length ? '' : `Nenhum ${tipo === 'fatura' ? 'cartão' : 'conta bancária'} cadastrado. <a href="#" id="lnkc">Cadastrar agora</a>`;
    const lk = el.querySelector('#lnkc'); if (lk) lk.onclick = e => { e.preventDefault(); editarConta(null, tipo === 'fatura' ? 'cartao' : 'banco', () => { ui.view = 'importar'; }); };
    el.querySelector('#fref').classList.toggle('hidden', tipo !== 'fatura');
  };
  el.querySelectorAll('#segtipo button').forEach(b => b.onclick = () => { tipo = b.dataset.t; atual(); });
  atual();
  const drop = el.querySelector('#drop'), inp = el.querySelector('#imfile');
  drop.onclick = () => inp.click();
  drop.ondragover = e => { e.preventDefault(); drop.classList.add('on'); };
  drop.ondragleave = () => drop.classList.remove('on');
  drop.ondrop = e => { e.preventDefault(); drop.classList.remove('on'); if (e.dataTransfer.files[0]) processar(e.dataTransfer.files[0]); };
  inp.onchange = () => inp.files[0] && processar(inp.files[0]);
  async function processar(file) {
    const err = el.querySelector('#imerr'); const contaId = el.querySelector('#imconta').value;
    if (!contaId) { err.textContent = 'Cadastre e escolha o cartão/conta de destino primeiro.'; return; }
    const ref = el.querySelector('#imref').value || mesAtual();
    err.textContent = 'Lendo ' + file.name + '…'; err.style.color = 'var(--cinza4)';
    try {
      const nome = file.name.toLowerCase(); let itens = [], totalLido = null, texto = '';
      if (nome.endsWith('.pdf')) {
        const pags = await textoPdf(await file.arrayBuffer());
        const linhas = pags.flat(); texto = linhas.join('\n');
        const r = lerLinhas(linhas, tipo, tipo === 'fatura' ? ref : mesAtual()); itens = r.itens; totalLido = r.totalLido;
        if (tipo === 'extrato') { // recalcula ano com base na maior data encontrada
          const mx = itens.map(i => i.data.slice(0, 7)).sort().pop(); if (mx) { const r2 = lerLinhas(linhas, tipo, mx > mesAtual() ? mesAtual() : mx); itens = r2.itens; }
        }
      } else {
        const txt = await file.text(); texto = txt.slice(0, 20000);
        itens = /<OFX>|OFXHEADER/i.test(txt) ? lerOFX(txt, tipo) : lerCSV(txt, tipo);
      }
      if (!itens.length) { err.style.color = ''; err.innerHTML = 'Não encontrei lançamentos neste arquivo. Se for PDF escaneado (imagem), use o OFX/CSV do banco. <a href="#" id="vtx">Ver texto extraído</a>'; const v = el.querySelector('#vtx'); if (v) v.onclick = ev => { ev.preventDefault(); modal(`<h3>Texto extraído</h3><div class="filete"></div><div class="pre">${esc(texto.slice(0, 15000)) || '(nenhum texto — provavelmente é imagem)'}</div><div class="acts"><button class="btn" id="fx">Fechar</button></div>`, {lg: true}).querySelector('#fx').onclick = fecharModal; }; return; }
      const existentes = new Set(S.lancamentos.filter(l => l.conta === contaId).map(l => chaveDup(contaId, l)));
      // (lançamentos que vieram do banco também contam como existentes)
      const fitids = new Set(S.lancamentos.filter(l => l.fitid).map(l => l.fitid));
      const vistos = new Set();
      itens = itens.map(i => {
        const mesRef = tipo === 'fatura' ? ref : i.data.slice(0, 7);
        const k = chaveDup(contaId, i); let dup = existentes.has(k) || (i.fitid && fitids.has(i.fitid));
        const k2 = k + '|' + (i.parcela || ''); const repetidoNoArquivo = vistos.has(k2); vistos.add(k2);
        let catId = aplicarRegras(i.desc);
        // possível duplicata de conta fixa já marcada como paga manualmente
        let dupFixa = !dup && S.lancamentos.some(l => l.origem === 'fixa' && l.mesRef === mesRef && Math.abs(Math.abs(l.valor) - Math.abs(i.valor)) < 0.01);
        return {...i, id: uid(), mesRef, cat: catId, sel: !dup && !dupFixa, dup, dupFixa, repetidoNoArquivo};
      });
      IMP = {itens, contaId, tipo, ref, totalLido, arquivo: file.name, texto};
      render();
    } catch (e) {
      err.style.color = ''; err.textContent = e && /password|senha/i.test(e.message || e.name) ? 'PDF protegido: senha não informada.' : 'Erro ao ler: ' + (e.message || e);
      console.error(e);
    }
  }
}
function vRevisao(el) {
  const I = IMP; const c = conta(I.contaId);
  const somaSel = () => I.itens.filter(i => i.sel).reduce((s, i) => s + i.valor, 0);
  const comprasSel = () => -I.itens.filter(i => i.sel && i.valor < 0).reduce((s, i) => s + i.valor, 0);
  el.innerHTML = topo('Revisar importação', {pessoa: false, extra: '<button class="btn" id="bcanc">Cancelar</button><button class="btn red" id="bimp">Importar selecionados</button>'}) + `
  <div class="grid g4">
    <div class="card kpi"><div class="lb">Arquivo</div><div class="v" style="font-size:15px;word-break:break-all">${esc(I.arquivo)}</div><div class="s">${esc(c?.nome || '')} · ${I.tipo === 'fatura' ? 'fatura de ' + nomeMes(I.ref) : 'extrato'}</div></div>
    <div class="card kpi"><div class="lb">Itens lidos</div><div class="v">${I.itens.length}</div><div class="s"><span id="nsel"></span> selecionados · ${I.itens.filter(i => i.dup).length} já existiam</div></div>
    <div class="card kpi"><div class="lb">${I.tipo === 'fatura' ? 'Compras selecionadas' : 'Saldo do selecionado'}</div><div class="v" id="ksoma"></div><div class="s" id="kdif"></div></div>
    <div class="card kpi"><div class="lb">Total lido no PDF</div><div class="v">${I.totalLido != null ? fmtR(I.totalLido) : '·'}</div><div class="s">${I.totalLido != null ? 'confira com a soma ao lado' : 'não identificado'}</div></div>
  </div>
  <div class="card" style="margin-top:16px">
    <div class="ctrl" style="margin-bottom:10px"><button class="btn sm" id="ball">Marcar todos</button><button class="btn sm" id="bnone">Desmarcar todos</button><span class="small muted">Clique no valor para inverter o sinal (entrada ↔ saída). <span class="tag warn">?</span> = sinal deduzido pelo texto, confira.</span><a href="#" id="vtx" class="small" style="margin-left:auto">Ver texto extraído</a></div>
    <div class="tw"><table class="t"><thead><tr><th></th><th>Data</th><th>Descrição</th><th>Parcela</th><th>Categoria</th><th class="r">Valor</th><th>Situação</th></tr></thead><tbody>
    ${I.itens.map(i => `<tr data-id="${i.id}" style="${i.sel ? '' : 'opacity:.55'}"><td><input type="checkbox" data-sel ${i.sel ? 'checked' : ''}></td>
      <td><input class="in" type="date" data-data value="${i.data}" style="padding:3px 6px;width:140px"></td>
      <td><input class="in" data-desc value="${esc(i.desc)}" style="padding:3px 6px;min-width:240px"></td>
      <td class="small">${esc(i.parcela || '')}</td>
      <td><select data-cat><option value="">— escolher —</option>${S.categorias.map(cc => `<option value="${cc.id}" ${i.cat === cc.id ? 'selected' : ''}>${esc(cc.nome)}</option>`).join('')}</select></td>
      <td class="r"><button class="btn sm ghost ${i.valor < 0 ? '' : 'pos'}" data-sinal style="font-weight:700">${fmtR(i.valor)}</button>${i.incerto ? ' <span class="tag warn" title="Sinal deduzido pelo texto">?</span>' : ''}</td>
      <td>${i.dup ? '<span class="tag red">já importado</span>' : i.dupFixa ? '<span class="tag warn">conta fixa já paga?</span>' : i.repetidoNoArquivo ? '<span class="tag warn">repetido no arquivo</span>' : '<span class="tag ok">novo</span>'}</td></tr>`).join('')}
    </tbody></table></div>
  </div>`;
  const upd = () => {
    el.querySelector('#nsel').textContent = I.itens.filter(i => i.sel).length;
    if (I.tipo === 'fatura') { const cs = comprasSel(), liq = -somaSel(); el.querySelector('#ksoma').textContent = fmtR(cs);
      el.querySelector('#kdif').innerHTML = `líquido (com estornos/pagamentos): ${fmtR(liq)}` + (I.totalLido != null ? `<br>${Math.abs(cs - I.totalLido) < 0.05 || Math.abs(liq - I.totalLido) < 0.05 ? '<b class="pos">bate com o total ✓</b>' : `diferença p/ total: ${fmtR(cs - I.totalLido)}`}` : '');
    } else { el.querySelector('#ksoma').textContent = fmtR(somaSel()); el.querySelector('#kdif').textContent = 'entradas − saídas'; }
  };
  upd();
  const item = tr => I.itens.find(i => i.id === tr.dataset.id);
  el.querySelectorAll('tr[data-id]').forEach(tr => {
    const it = item(tr);
    tr.querySelector('[data-sel]').onchange = e => { it.sel = e.target.checked; tr.style.opacity = it.sel ? '' : '.55'; upd(); };
    tr.querySelector('[data-data]').onchange = e => { it.data = e.target.value; if (I.tipo !== 'fatura') it.mesRef = it.data.slice(0, 7); };
    tr.querySelector('[data-desc]').onchange = e => { it.desc = e.target.value; };
    tr.querySelector('[data-cat]').onchange = e => {
      it.cat = e.target.value;
      // aplica a mesma categoria a itens com descrição parecida ainda sem categoria
      const base = norm(it.desc).split(' ').slice(0, 2).join(' '); let n = 0;
      for (const o of I.itens) if (o !== it && !o.cat && norm(o.desc).startsWith(base)) { o.cat = it.cat; n++; }
      if (it.cat && !I.regrasPend) I.regrasPend = {}; if (it.cat) I.regrasPend[base] = it.cat;
      if (n) { toast(`${n} item(ns) parecido(s) também classificado(s)`); render(); }
    };
    tr.querySelector('[data-sinal]').onclick = e => { it.valor = -it.valor; it.incerto = false; render(); };
  });
  el.querySelector('#ball').onclick = () => { I.itens.forEach(i => i.sel = true); render(); };
  el.querySelector('#bnone').onclick = () => { I.itens.forEach(i => i.sel = false); render(); };
  el.querySelector('#bcanc').onclick = () => { IMP = null; render(); };
  el.querySelector('#vtx').onclick = e => { e.preventDefault(); modal(`<h3>Texto extraído do arquivo</h3><div class="small muted">Útil para conferir se algum item ficou de fora.</div><div class="filete"></div><div class="pre">${esc(I.texto.slice(0, 30000))}</div><div class="acts"><button class="btn" id="fx">Fechar</button></div>`, {lg: true}).querySelector('#fx').onclick = fecharModal; };
  el.querySelector('#bimp').onclick = () => {
    const sel = I.itens.filter(i => i.sel); if (!sel.length) return toast('Nenhum item selecionado.');
    for (const i of sel) S.lancamentos.push({id: uid(), data: i.data, mesRef: i.mesRef, desc: i.desc, valor: Math.round(i.valor * 100) / 100, cat: i.cat, conta: I.contaId, parcela: i.parcela, origem: 'importado', fitid: i.fitid || undefined, autor: USER.nome});
    // regras aprendidas na revisão
    let nr = 0; for (const [termo, cid] of Object.entries(I.regrasPend || {})) if (termo.length >= 3 && !S.regras.some(r => norm(r.termo) === termo)) { S.regras.push({id: uid(), termo, cat: cid}); nr++; }
    salvar(true); const n = sel.length, ref = sel[0].mesRef; IMP = null; ui.mes = ref; ui.view = 'lancamentos'; ui.filtro = {conta: I.contaId};
    toast(`${n} lançamento(s) importado(s)` + (nr ? ` · ${nr} regra(s) de categoria criada(s)` : '')); render();
  };
}

/* =====================================================================
   CONTAS FIXAS
   ===================================================================== */
function vFixas(el) {
  const m = ui.mes, fx = fixasVisiveis().sort((a, b) => (a.dia || 0) - (b.dia || 0)), pg = S.pagFixas[m] || {};
  const prev = fx.reduce((s, f) => s + (f.valor || 0), 0), pago = fx.reduce((s, f) => s + (pg[f.id]?.valor || 0), 0);
  const inativas = S.fixas.filter(f => f.ativa === false);
  el.innerHTML = topo('Contas fixas', {mes: true, extra: '<button class="btn pri" id="bnova">+ Nova conta fixa</button>'}) + `
  <div class="grid g3">
    <div class="card kpi"><div class="lb">Previsto no mês</div><div class="v">${fmtR(prev)}</div><div class="s">${fx.length} contas ativas</div></div>
    <div class="card kpi"><div class="lb">Pago</div><div class="v pos">${fmtR(pago)}</div><div class="s">${Object.keys(pg).filter(id => fx.some(f => f.id === id)).length} de ${fx.length}</div></div>
    <div class="card kpi dest"><div class="lb">Falta pagar</div><div class="v">${fmtR(Math.max(0, fx.filter(f => !pg[f.id]).reduce((s, f) => s + (f.valor || 0), 0)))}</div></div>
  </div>
  <div class="card" style="margin-top:16px">
    ${fx.length ? `<div class="tw"><table class="t"><thead><tr><th>Vence</th><th>Conta</th><th>Categoria</th><th>Pagar por</th>${S.pessoas.length > 1 ? '<th>De quem</th>' : ''}<th>Boleto vem de</th><th class="r">Previsto</th><th>Situação</th><th></th></tr></thead><tbody>
    ${fx.map(f => { const p = pg[f.id]; const v = vencimentoFixa(f, m); const d = diasEntre(hoje(), v); const fi = S.filhos.find(x => x.id === f.filho); const rec = S.cobrancas[m]?.[f.id];
      return `<tr><td><b>${String(f.dia).padStart(2, '0')}</b></td><td>${esc(f.nome)}${f.privado ? ' 🔒' : ''}${f.obs ? `<div class="small muted">${esc(f.obs)}</div>` : ''}</td><td class="small">${esc(cat(f.cat).nome)}</td><td class="small">${esc(conta(f.conta)?.nome || f.forma || '')}</td>${S.pessoas.length > 1 ? `<td class="small">${esc(nomePessoa(f.dono || 'casal'))}</td>` : ''}
      <td class="small">${fi ? esc(fi.nome) + (p ? '' : rec ? ' <span class="tag ok">recebido</span>' : ' <span class="tag warn">aguardando</span>') : '·'}</td>
      <td class="r">${fmtR(f.valor)}</td>
      <td>${p ? `<span class="tag ok">pago ${fmtData(p.data)} · ${fmtR(p.valor)}</span>` : d < 0 ? `<span class="tag red">vencida</span>` : d <= 5 ? `<span class="tag warn">vence em ${d}d</span>` : '<span class="tag">em aberto</span>'}</td>
      <td class="r" style="white-space:nowrap">${p ? `<button class="btn sm ghost" data-desf="${f.id}">Desfazer</button>` : `<button class="btn sm" data-pagar="${f.id}">Pagar</button>`} <button class="btn sm ghost" data-ed="${f.id}">Editar</button></td></tr>`; }).join('')}
    </tbody></table></div>` : '<div class="vazio">Cadastre aluguel/condomínio, luz, água, internet, escola, plano de saúde, seguros, assinaturas… e acompanhe mês a mês o que já foi pago.</div>'}
  </div>
  ${inativas.length ? `<div class="card" style="margin-top:16px"><h3>Desativadas</h3>${inativas.map(f => `<span class="tag" style="margin:2px;cursor:pointer" data-ed="${f.id}">${esc(f.nome)}</span>`).join('')}</div>` : ''}`;
  ligarTopo(el);
  el.querySelector('#bnova').onclick = () => editarFixa();
  el.querySelectorAll('[data-ed]').forEach(b => b.onclick = () => editarFixa(S.fixas.find(f => f.id === b.dataset.ed)));
  el.querySelectorAll('[data-pagar]').forEach(b => b.onclick = () => pagarFixa(b.dataset.pagar, m));
  el.querySelectorAll('[data-desf]').forEach(b => b.onclick = () => {
    const p = S.pagFixas[m][b.dataset.desf]; if (p?.lanc) S.lancamentos = S.lancamentos.filter(l => l.id !== p.lanc);
    delete S.pagFixas[m][b.dataset.desf]; salvar(); render();
  });
}
function editarFixa(f) {
  const novo = !f; f = f || {dia: 10, ativa: true, dono: ui.pessoa !== 'todos' ? ui.pessoa : 'casal'};
  formModal(novo ? 'Nova conta fixa' : 'Editar conta fixa', [
    {k: 'nome', label: 'Nome', req: true, ph: 'Ex.: Condomínio, Luz, Escola do João'},
    {k: 'valor', label: 'Valor previsto (R$)', type: 'money', half: true},
    {k: 'dia', label: 'Dia do vencimento', type: 'number', min: 1, max: 31, half: true},
    {k: 'cat', label: 'Categoria', type: 'select', options: optCats(['despesa', 'reserva']), vazio: '—', half: true},
    {k: 'conta', label: 'Paga por (conta/cartão)', type: 'select', options: optContas(), vazio: '— definir na hora —', half: true},
    ...(S.pessoas.length > 1 ? [{k: 'dono', label: 'De quem é a conta', type: 'select', options: optPessoas(), half: true}] : []),
    {k: 'filho', label: 'Boleto enviado por (filho)', type: 'select', options: S.filhos.map(x => [x.id, x.nome]), vazio: '— não depende de filho —', half: true, help: 'O filho será lembrado de mandar esta conta.'},
    {k: 'obs', label: 'Observação'},
    CAMPO_PRIV(),
    {k: 'ativa', label: 'Ativa', type: 'checkbox'},
  ], f, v => { Object.assign(f, v); f.dia = Math.min(31, Math.max(1, +v.dia || 1)); if (novo) { f.id = uid(); f.desde = ui.mes < mesAtual() ? ui.mes : mesAtual(); S.fixas.push(f); } },
  {aoExcluir: novo ? null : () => { S.fixas = S.fixas.filter(x => x.id !== f.id); }});
}
function pagarFixa(id, m) {
  const f = S.fixas.find(x => x.id === id);
  formModal('Registrar pagamento', [
    {k: 'valor', label: 'Valor pago (R$)', type: 'money', req: true, half: true},
    {k: 'data', label: 'Data do pagamento', type: 'date', req: true, half: true},
    {k: 'conta', label: 'Pago com', type: 'select', options: optContas(), vazio: '— sem conta —'},
    {k: 'lancar', label: 'Criar lançamento de despesa', type: 'checkbox', help: 'Desmarque se esse pagamento já vai entrar pela importação do extrato/fatura (evita contar em dobro).'},
  ], {valor: f.valor, data: hoje() < vencimentoFixa(f, m) ? hoje() : vencimentoFixa(f, m), conta: f.conta, lancar: true}, v => {
    S.pagFixas[m] = S.pagFixas[m] || {};
    let lanc = null;
    if (v.lancar) { lanc = uid(); S.lancamentos.push({id: lanc, data: v.data, mesRef: m, desc: f.nome, valor: -Math.abs(v.valor), cat: f.cat, conta: v.conta, dono: f.dono || '', origem: 'fixa', fixa: f.id, autor: USER.nome}); }
    S.pagFixas[m][f.id] = {valor: Math.abs(v.valor), data: v.data, conta: v.conta, lanc, por: USER.nome};
  }, {sub: f.nome + ' · ' + nomeMes(m)});
}

/* =====================================================================
   FILHOS — cobrança das contas
   ===================================================================== */
function pendenciasFilho(fi, m) { return S.fixas.filter(f => f.ativa !== false && (!f.desde || f.desde <= m) && f.filho === fi.id && !S.pagFixas[m]?.[f.id] && !S.cobrancas[m]?.[f.id]); }
function abrirWhats(filhoId, m) {
  const fi = S.filhos.find(x => x.id === filhoId); const pend = pendenciasFilho(fi, m);
  const lista = (pend.length ? pend : S.fixas.filter(f => f.filho === fi.id && f.ativa !== false)).map(f => `• ${f.nome} (vence dia ${f.dia})`).join('\n');
  const txt = (S.config.msgWhats || '').replace(/\{nome\}/g, fi.nome.split(' ')[0]).replace(/\{mes\}/g, MESES[+m.slice(5) - 1]).replace(/\{lista\}/g, lista);
  const num = String(fi.whats || '').replace(/\D/g, ''); const tel = num.length <= 11 ? '55' + num : num;
  const box = modal(`<h3>Cobrar ${esc(fi.nome)}</h3><div class="filete"></div><div class="fld"><label>Mensagem</label><textarea class="in" id="wmsg" style="min-height:150px">${esc(txt)}</textarea></div>
    <div class="acts"><button class="btn" id="wc">Copiar</button><button class="btn wa" id="wo" ${num ? '' : 'disabled'}>Abrir no WhatsApp</button></div>${num ? '' : '<div class="erro">Cadastre o WhatsApp deste filho.</div>'}`);
  box.querySelector('#wc').onclick = () => { navigator.clipboard.writeText(box.querySelector('#wmsg').value).then(() => toast('Mensagem copiada')); };
  box.querySelector('#wo').onclick = () => {
    window.open('https://wa.me/' + tel + '?text=' + encodeURIComponent(box.querySelector('#wmsg').value), '_blank', 'noopener');
    fi.ultimaCobranca = new Date().toISOString(); salvar(); fecharModal(); render();
  };
}
function vFilhos(el) {
  const m = ui.mes;
  el.innerHTML = topo('Cobrança dos filhos', {mes: true, pessoa: false, extra: '<button class="btn pri" id="bnovo">+ Cadastrar filho</button>'}) + `
  <div class="small muted" style="margin:-6px 0 14px">Vincule as contas fixas ao filho que deve mandar o boleto (em <b>Contas fixas → Boleto enviado por</b>). A partir do dia de cobrança, o painel mostra quem está devendo envio, com a mensagem pronta para o WhatsApp.</div>
  ${S.filhos.length ? '<div class="grid g2">' + S.filhos.map(fi => { const cs = S.fixas.filter(f => f.filho === fi.id && f.ativa !== false);
    return `<div class="card"><h3>${esc(fi.nome)} <span class="x"><button class="btn sm ghost" data-ed="${fi.id}">Editar</button> <button class="btn sm wa" data-wa="${fi.id}">Cobrar no WhatsApp</button></span></h3>
      <div class="small muted" style="margin-bottom:8px">${fi.whats ? 'WhatsApp ' + esc(fi.whats) : 'sem WhatsApp cadastrado'} · cobrar a partir do dia ${fi.dia || 1}${fi.ultimaCobranca ? ' · última cobrança ' + fmtData(fi.ultimaCobranca.slice(0, 10)) : ''}</div>
      ${cs.length ? `<table class="t"><tbody>${cs.map(f => { const pg = S.pagFixas[m]?.[f.id], rec = S.cobrancas[m]?.[f.id];
        return `<tr><td>${esc(f.nome)}<div class="small muted">vence dia ${f.dia} · ${fmtR(f.valor)}</div></td><td class="r">${pg ? '<span class="tag ok">paga</span>' : rec ? `<span class="tag ok">recebida</span> <button class="btn sm ghost" data-rec="${f.id}">desfazer</button>` : `<span class="tag warn">aguardando</span> <button class="btn sm" data-rec="${f.id}">Recebi</button>`}</td></tr>`; }).join('')}</tbody></table>` : '<div class="vazio small">Nenhuma conta vinculada.</div>'}</div>`; }).join('') + '</div>'
    : '<div class="card"><div class="vazio">Cadastre seus filhos para lembrar de cobrar o envio das contas (escola, faculdade, aluguel, celular…).</div></div>'}`;
  ligarTopo(el);
  el.querySelector('#bnovo').onclick = () => editarFilho();
  el.querySelectorAll('[data-ed]').forEach(b => b.onclick = () => editarFilho(S.filhos.find(x => x.id === b.dataset.ed)));
  el.querySelectorAll('[data-wa]').forEach(b => b.onclick = () => abrirWhats(b.dataset.wa, m));
  el.querySelectorAll('[data-rec]').forEach(b => b.onclick = () => { S.cobrancas[m] = S.cobrancas[m] || {}; if (S.cobrancas[m][b.dataset.rec]) delete S.cobrancas[m][b.dataset.rec]; else S.cobrancas[m][b.dataset.rec] = {em: hoje(), por: USER.nome}; salvar(); render(); });
}
function editarFilho(fi) {
  const novo = !fi; fi = fi || {dia: 1};
  formModal(novo ? 'Cadastrar filho' : 'Editar filho', [
    {k: 'nome', label: 'Nome', req: true},
    {k: 'whats', label: 'WhatsApp (com DDD)', ph: '(24) 99999-9999', half: true},
    {k: 'dia', label: 'Cobrar a partir do dia', type: 'number', min: 1, max: 28, half: true},
  ], fi, v => { Object.assign(fi, v); if (novo) { fi.id = uid(); S.filhos.push(fi); } },
  {aoExcluir: novo ? null : () => { S.filhos = S.filhos.filter(x => x.id !== fi.id); S.fixas.forEach(f => { if (f.filho === fi.id) f.filho = ''; }); }});
}

/* =====================================================================
   CARTÕES E CONTAS
   ===================================================================== */
function vContas(el) {
  const m = ui.mes; const cs = S.contas.filter(c => passaPessoa(c.dono));
  const card = c => {
    const ls = S.lancamentos.filter(l => l.conta === c.id && l.mesRef === m);
    const tot = -ls.filter(l => cat(l.cat).tipo !== 'neutro').reduce((s, l) => s + l.valor, 0);
    const prog = S.milhas.find(p => p.id === c.programa);
    return `<div class="card"><h3>${c.tipo === 'cartao' ? '▭' : '⌂'} ${esc(c.nome)}${c.privado ? ' 🔒' : ''}${c.origem === 'openfinance' || Object.values(S.config.mapaPluggy || {}).includes(c.id) ? ' <span class="tag ok">conectado</span>' : ''} <span class="x"><button class="btn sm ghost" data-ed="${c.id}">Editar</button></span></h3>
      <div class="small muted">${esc(c.banco || '')}${c.final ? ' · final ' + esc(c.final) : ''}${S.pessoas.length > 1 ? ' · ' + esc(nomePessoa(c.dono)) : ''}</div>
      ${c.tipo === 'cartao' ? `<div class="kpi" style="margin-top:10px"><div class="lb">Fatura de ${nomeMes(m)}</div><div class="v">${fmtR(tot)}</div><div class="s">fecha dia ${c.fechamento || '·'} · vence dia ${c.vencimento || '·'} · ${ls.length} itens</div></div>
        ${c.limite ? `<div class="bar" style="margin-top:8px"><i class="${tot / c.limite > 0.8 ? 'red' : ''}" style="width:${Math.min(100, tot / c.limite * 100)}%"></i></div><div class="small muted">${fmtPct(tot / c.limite)} do limite de ${fmtR(c.limite)}</div>` : ''}
        ${prog ? `<div class="small" style="margin-top:6px">Acumula em <b>${esc(prog.programa)}</b>${c.ptsDolar ? ` · ${c.ptsDolar} pts/US$` : ''}</div>` : ''}`
      : `<div class="kpi" style="margin-top:10px"><div class="lb">Movimento em ${nomeMes(m)}</div><div class="v">${fmtR(ls.reduce((s, l) => s + l.valor, 0))}</div><div class="s">${ls.length} lançamentos</div></div>`}
      <div style="margin-top:10px"><button class="btn sm" data-ver="${c.id}">Ver lançamentos</button></div></div>`;
  };
  el.innerHTML = topo('Cartões e contas', {mes: true, extra: '<button class="btn" id="bnb">+ Conta bancária</button><button class="btn pri" id="bnc">+ Cartão</button>'}) +
    `<h3 class="muted small" style="text-transform:uppercase;letter-spacing:.6px">Cartões de crédito</h3><div class="grid g3">${cs.filter(c => c.tipo === 'cartao').map(card).join('') || '<div class="card vazio">Nenhum cartão.</div>'}</div>
     <h3 class="muted small" style="text-transform:uppercase;letter-spacing:.6px;margin-top:22px">Contas bancárias</h3><div class="grid g3">${cs.filter(c => c.tipo === 'banco').map(card).join('') || '<div class="card vazio">Nenhuma conta.</div>'}</div>`;
  ligarTopo(el);
  el.querySelector('#bnc').onclick = () => editarConta(null, 'cartao');
  el.querySelector('#bnb').onclick = () => editarConta(null, 'banco');
  el.querySelectorAll('[data-ed]').forEach(b => b.onclick = () => editarConta(S.contas.find(c => c.id === b.dataset.ed)));
  el.querySelectorAll('[data-ver]').forEach(b => b.onclick = () => { ui.filtro = {conta: b.dataset.ver}; ui.view = 'lancamentos'; render(); });
}
function editarConta(c, tipo, depois) {
  const novo = !c; c = c || {tipo, dono: ui.pessoa !== 'todos' ? ui.pessoa : (USER.pessoa || 'casal')};
  const cartao = c.tipo === 'cartao';
  formModal(novo ? (cartao ? 'Novo cartão' : 'Nova conta bancária') : 'Editar', [
    {k: 'nome', label: 'Nome', req: true, ph: cartao ? 'Ex.: Itaú Visa Infinite' : 'Ex.: Itaú conta corrente'},
    {k: 'banco', label: 'Banco', type: 'select', options: ['Itaú', 'Bradesco', 'Nubank', 'Banco do Brasil', 'Caixa', 'XP', 'Santander', 'Inter', 'C6', 'BTG', 'Outro'].map(x => [x, x]), half: true},
    {k: 'final', label: 'Últimos 4 dígitos (opcional)', half: true, ph: '1234'},
    ...(S.pessoas.length > 1 ? [{k: 'dono', label: 'Titular', type: 'select', options: optPessoas()}] : []), CAMPO_PRIV(),
    ...(cartao ? [
      {k: 'fechamento', label: 'Dia de fechamento', type: 'number', min: 1, max: 31, half: true},
      {k: 'vencimento', label: 'Dia de vencimento', type: 'number', min: 1, max: 31, half: true},
      {k: 'limite', label: 'Limite (R$)', type: 'money', half: true},
      {k: 'ptsDolar', label: 'Pontos por US$', type: 'number', step: '0.1', half: true},
      {k: 'programa', label: 'Programa de pontos vinculado', type: 'select', options: S.milhas.map(p => [p.id, p.programa]), vazio: '— nenhum —'},
    ] : []),
  ], c, v => { v.final = String(v.final || '').replace(/\D/g, '').slice(-4); Object.assign(c, v); if (novo) { c.id = uid(); S.contas.push(c); } if (depois) depois(); },
  {aoExcluir: novo ? null : () => { const n = S.lancamentos.filter(l => l.conta === c.id).length; if (n && !confirm(`Esta conta tem ${n} lançamentos. Eles ficarão sem conta. Continuar?`)) return; S.contas = S.contas.filter(x => x.id !== c.id); }});
}

/* =====================================================================
   MILHAS
   ===================================================================== */
function vMilhas(el) {
  const ps = S.milhas.filter(p => passaPessoa(p.dono || 'casal'));
  const tot = ps.reduce((s, p) => s + (p.saldo || 0), 0), val = ps.reduce((s, p) => s + (p.saldo || 0) / 1000 * (p.milheiro || 0), 0);
  el.innerHTML = topo('Milhas e pontos', {extra: '<button class="btn pri" id="bnovo">+ Programa</button>'}) + `
  <div class="grid g3"><div class="card kpi"><div class="lb">Total de pontos</div><div class="v">${fmtN(tot)}</div></div>
  <div class="card kpi"><div class="lb">Valor estimado</div><div class="v">${fmtR(val)}</div><div class="s">pelo valor do milheiro informado</div></div>
  <div class="card kpi dest"><div class="lb">Vencendo em 90 dias</div><div class="v">${fmtN(ps.filter(p => p.vencimento && diasEntre(hoje(), p.vencimento) <= 90 && diasEntre(hoje(), p.vencimento) >= 0).reduce((s, p) => s + (p.aVencer || 0), 0))}</div></div></div>
  <div class="card" style="margin-top:16px">${ps.length ? `<div class="tw"><table class="t"><thead><tr><th>Programa</th>${S.pessoas.length > 1 ? '<th>Titular</th>' : ''}<th class="r">Saldo</th><th class="r">Milheiro</th><th class="r">Valor est.</th><th>Próximo vencimento</th><th>Cartões</th><th>Atualizado</th><th></th></tr></thead><tbody>
  ${ps.map(p => { const d = p.vencimento ? diasEntre(hoje(), p.vencimento) : null; const cts = S.contas.filter(c => c.programa === p.id);
    return `<tr><td><b>${esc(p.programa)}</b>${p.privado ? ' 🔒' : ''}${p.obs ? `<div class="small muted">${esc(p.obs)}</div>` : ''}</td>${S.pessoas.length > 1 ? `<td class="small">${esc(nomePessoa(p.dono || 'casal'))}</td>` : ''}<td class="r"><b>${fmtN(p.saldo)}</b></td><td class="r">${p.milheiro ? fmtR(p.milheiro) : '·'}</td><td class="r">${fmtR((p.saldo || 0) / 1000 * (p.milheiro || 0))}</td>
    <td>${p.vencimento ? `${fmtN(p.aVencer || 0)} em ${fmtData(p.vencimento)} ${d != null && d <= 60 && d >= 0 ? `<span class="tag ${d <= 15 ? 'red' : 'warn'}">${d}d</span>` : d < 0 ? '<span class="tag">passou</span>' : ''}` : '·'}</td>
    <td class="small">${cts.map(c => esc(c.nome)).join(', ') || '·'}</td><td class="small muted">${p.atualizado ? fmtData(p.atualizado) : '·'}</td><td class="r"><button class="btn sm ghost" data-ed="${p.id}">Editar</button></td></tr>`; }).join('')}</tbody></table></div>` : '<div class="vazio">Cadastre Smiles, LATAM Pass, TudoAzul, Livelo, Esfera, Átomos… com saldo e vencimento para ser avisado antes de perder pontos.</div>'}</div>`;
  ligarTopo(el);
  el.querySelector('#bnovo').onclick = () => editarMilha();
  el.querySelectorAll('[data-ed]').forEach(b => b.onclick = () => editarMilha(S.milhas.find(p => p.id === b.dataset.ed)));
}
function editarMilha(p) {
  const novo = !p; p = p || {dono: USER.pessoa || 'casal', milheiro: 20};
  formModal(novo ? 'Novo programa' : 'Editar programa', [
    {k: 'programa', label: 'Programa', req: true, ph: 'Smiles, LATAM Pass, Livelo, Esfera…'},
    ...(S.pessoas.length > 1 ? [{k: 'dono', label: 'Titular', type: 'select', options: optPessoas()}] : []), CAMPO_PRIV(),
    {k: 'saldo', label: 'Saldo atual (pontos)', type: 'number', half: true},
    {k: 'milheiro', label: 'Valor do milheiro (R$)', type: 'money', half: true, help: 'Referência para estimar valor.'},
    {k: 'aVencer', label: 'Pontos a vencer', type: 'number', half: true},
    {k: 'vencimento', label: 'Data do vencimento', type: 'date', half: true},
    {k: 'obs', label: 'Observação (clube, categoria…)'},
  ], p, v => { Object.assign(p, v); p.atualizado = hoje(); if (novo) { p.id = uid(); S.milhas.push(p); } },
  {aoExcluir: novo ? null : () => { S.milhas = S.milhas.filter(x => x.id !== p.id); }});
}

/* =====================================================================
   INVESTIMENTOS
   ===================================================================== */
const TIPOS_INV = ['Renda fixa (CDB/LCI/LCA)', 'Tesouro Direto', 'Fundos', 'Ações', 'FIIs', 'Previdência', 'Poupança', 'Cripto', 'Exterior', 'Imóveis', 'Outros'];
function vInvest(el) {
  const is = S.investimentos.filter(i => passaPessoa(i.dono || 'casal'));
  const apl = is.reduce((s, i) => s + (i.aplicado || 0), 0), atu = is.reduce((s, i) => s + (i.atual || 0), 0);
  const porTipo = {}; is.forEach(i => porTipo[i.tipo] = (porTipo[i.tipo] || 0) + (i.atual || 0));
  const liq = is.filter(i => i.liquidez === 'diaria').reduce((s, i) => s + (i.atual || 0), 0);
  el.innerHTML = topo('Investimentos', {extra: '<button class="btn pri" id="bnovo">+ Investimento</button>'}) + `
  <div class="grid g4"><div class="card kpi"><div class="lb">Patrimônio investido</div><div class="v">${fmtR(atu)}</div></div>
  <div class="card kpi"><div class="lb">Total aplicado</div><div class="v">${fmtR(apl)}</div></div>
  <div class="card kpi"><div class="lb">Resultado</div><div class="v ${atu - apl >= 0 ? 'pos' : 'neg'}">${fmtR(atu - apl)}</div><div class="s">${apl ? fmtPct(atu / apl - 1) : ''}</div></div>
  <div class="card kpi dest"><div class="lb">Liquidez diária</div><div class="v">${fmtR(liq)}</div><div class="s">disponível para emergências</div></div></div>
  <div class="grid g2" style="margin-top:16px">
    <div class="card"><h3>Distribuição</h3>${Object.keys(porTipo).length ? Object.entries(porTipo).sort((a, b) => b[1] - a[1]).map(([t, v]) => `<div class="catrow"><div class="n">${esc(t)}</div><div class="bar"><i style="width:${v / atu * 100}%"></i></div><div class="val">${fmtR(v)}<div class="lim">${fmtPct(v / atu)}</div></div></div>`).join('') : '<div class="vazio">—</div>'}</div>
    <div class="card"><h3>Dica</h3><div class="small">Vincule cada investimento a uma meta (viagem, aposentadoria, emergência) para acompanhar automaticamente quanto já foi guardado para cada objetivo. Atualize o "valor atual" uma vez por mês, olhando o app da corretora.</div></div>
  </div>
  <div class="card" style="margin-top:16px">${is.length ? `<div class="tw"><table class="t"><thead><tr><th>Investimento</th><th>Tipo</th><th>Instituição</th>${S.pessoas.length > 1 ? '<th>Titular</th>' : ''}<th>Meta</th><th>Liquidez</th><th class="r">Aplicado</th><th class="r">Atual</th><th>Atualizado</th><th></th></tr></thead><tbody>
  ${is.map(i => `<tr><td><b>${esc(i.nome)}</b>${i.privado ? ' 🔒' : ''}${i.venc ? `<div class="small muted">vence ${fmtData(i.venc)}</div>` : ''}</td><td class="small">${esc(i.tipo)}</td><td class="small">${esc(i.inst || '')}</td>${S.pessoas.length > 1 ? `<td class="small">${esc(nomePessoa(i.dono || 'casal'))}</td>` : ''}<td class="small">${esc(S.metas.find(m => m.id === i.meta)?.nome || '·')}</td><td class="small">${i.liquidez === 'diaria' ? 'diária' : i.liquidez === 'venc' ? 'no vencimento' : 'D+' + (i.liquidez || '?')}</td><td class="r">${fmtR(i.aplicado)}</td><td class="r"><b>${fmtR(i.atual)}</b></td><td class="small muted">${i.atualizado ? fmtData(i.atualizado) : ''}</td><td class="r"><button class="btn sm ghost" data-ed="${i.id}">Editar</button></td></tr>`).join('')}
  <tr class="tot"><td colspan="${S.pessoas.length > 1 ? 6 : 5}">Total</td><td class="r">${fmtR(apl)}</td><td class="r">${fmtR(atu)}</td><td></td><td></td></tr></tbody></table></div>` : '<div class="vazio">Cadastre seus investimentos (CDB, Tesouro, previdência, ações…).</div>'}</div>`;
  ligarTopo(el);
  el.querySelector('#bnovo').onclick = () => editarInv();
  el.querySelectorAll('[data-ed]').forEach(b => b.onclick = () => editarInv(S.investimentos.find(i => i.id === b.dataset.ed)));
}
function editarInv(i) {
  const novo = !i; i = i || {tipo: TIPOS_INV[0], liquidez: 'diaria', dono: USER.pessoa || 'casal'};
  formModal(novo ? 'Novo investimento' : 'Editar investimento', [
    {k: 'nome', label: 'Nome', req: true, ph: 'Ex.: CDB 110% CDI 2028'},
    {k: 'tipo', label: 'Tipo', type: 'select', options: TIPOS_INV.map(t => [t, t]), half: true},
    {k: 'inst', label: 'Instituição', half: true, ph: 'XP, Itaú, Nubank…'},
    {k: 'aplicado', label: 'Valor aplicado (R$)', type: 'money', half: true},
    {k: 'atual', label: 'Valor atual (R$)', type: 'money', half: true},
    {k: 'liquidez', label: 'Liquidez', type: 'select', options: [['diaria', 'Diária'], ['30', 'D+30'], ['90', 'D+90'], ['venc', 'Só no vencimento']], half: true},
    {k: 'venc', label: 'Vencimento', type: 'date', half: true},
    {k: 'meta', label: 'Meta vinculada', type: 'select', options: S.metas.map(m => [m.id, m.nome]), vazio: '— nenhuma —', half: true},
    ...(S.pessoas.length > 1 ? [{k: 'dono', label: 'Titular', type: 'select', options: optPessoas(), half: true}] : []),
    CAMPO_PRIV(),
  ], i, v => { Object.assign(i, v); i.atualizado = hoje(); if (novo) { i.id = uid(); S.investimentos.push(i); } },
  {aoExcluir: novo ? null : () => { S.investimentos = S.investimentos.filter(x => x.id !== i.id); }});
}

/* =====================================================================
   METAS / RESERVAS
   ===================================================================== */
const TIPO_META = {emergencia: 'Reserva de emergência', viagem: 'Viagem', aposentadoria: 'Aposentadoria', outro: 'Outro objetivo'};
function mesesAte(data) { if (!data) return 0; const [y, m] = data.split('-').map(Number); const [hy, hm] = mesAtual().split('-').map(Number); return Math.max(0, (y - hy) * 12 + (m - hm)); }
function aporteNecessario(mt) {
  const n = mesesAte(mt.data), S0 = saldoMeta(mt), falta = (mt.alvo || 0) - S0;
  if (falta <= 0) return 0; if (!n) return falta;
  const i = Math.pow(1 + (mt.rent || 0) / 100, 1 / 12) - 1;
  if (i <= 0) return falta / n;
  const f = Math.pow(1 + i, n); return Math.max(0, ((mt.alvo || 0) - S0 * f) * i / (f - 1));
}
function vMetas(el) {
  const ms = S.metas.filter(x => passaPessoa(x.dono || 'casal'));
  const somaAp = ms.reduce((s, m) => s + aporteNecessario(m), 0), sobra = sobraMedia(mesAtual()), med = mediaDesp(mesAtual());
  const temEmerg = ms.some(m => m.tipo === 'emergencia');
  el.innerHTML = topo('Reservas e metas', {extra: '<button class="btn pri" id="bnova">+ Nova meta</button>'}) + `
  <div class="grid g3">
    <div class="card kpi"><div class="lb">Guardar por mês (todas as metas)</div><div class="v">${fmtR(somaAp)}</div><div class="s">para cumprir os prazos</div></div>
    <div class="card kpi"><div class="lb">Sobra média (3 meses)</div><div class="v ${sobra >= 0 ? 'pos' : 'neg'}">${fmtR(sobra)}</div><div class="s">receitas − despesas</div></div>
    <div class="card kpi dest"><div class="lb">Cabe no orçamento?</div><div class="v ${sobra >= somaAp ? 'pos' : 'neg'}">${!somaAp ? '·' : sobra >= somaAp ? 'Sim' : 'Falta ' + fmtR(somaAp - sobra)}</div><div class="s">${somaAp && sobra < somaAp ? 'reduza gastos ou alongue prazos' : ''}</div></div>
  </div>
  ${!temEmerg && med > 0 ? `<div class="alert warn" style="margin-top:16px"><div class="tx"><b>Sugestão: reserva de emergência de ${fmtR(med * 6)}</b><span class="small muted">6 meses da sua despesa média (${fmtR(med)}/mês). Deve ficar em aplicação de liquidez diária.</span></div><button class="btn sm" id="bsug">Criar</button></div>` : ''}
  <div class="grid g2" style="margin-top:16px">${ms.length ? ms.map(mt => { const sd = saldoMeta(mt), p = mt.alvo ? sd / mt.alvo : 0, ap = aporteNecessario(mt), n = mesesAte(mt.data); const invs = S.investimentos.filter(i => i.meta === mt.id);
    return `<div class="card"><h3>${esc(mt.nome)}${mt.privado ? ' 🔒' : ''} <span class="tag ${mt.tipo === 'emergencia' ? 'red' : 'dark'}">${esc(TIPO_META[mt.tipo])}</span><span class="x"><button class="btn sm ghost" data-ed="${mt.id}">Editar</button></span></h3>
      <div style="display:flex;justify-content:space-between;align-items:end"><div class="kpi"><div class="v">${fmtR(sd)}</div><div class="s">de ${fmtR(mt.alvo)}${S.pessoas.length > 1 ? ' · ' + esc(nomePessoa(mt.dono || 'casal')) : ''}</div></div><div style="text-align:right"><b style="font-size:20px">${fmtPct(p)}</b></div></div>
      <div class="bar" style="margin:10px 0"><i class="${p >= 1 ? 'ok' : mt.tipo === 'emergencia' ? 'red' : ''}" style="width:${Math.min(100, p * 100)}%"></i></div>
      <div class="list small">
        <div class="it"><div class="grow">Prazo</div><b>${mt.data ? fmtData(mt.data) + ` (${n} meses)` : 'sem prazo'}</b></div>
        <div class="it"><div class="grow">Guardar por mês</div><b>${p >= 1 ? 'meta atingida ✓' : fmtR(ap)}</b></div>
        <div class="it"><div class="grow">Rentabilidade considerada</div><b>${fmtN(mt.rent || 0, 1)}% a.a.</b></div>
        ${mt.tipo === 'aposentadoria' && mt.renda ? `<div class="it"><div class="grow">Renda mensal desejada</div><b>${fmtR(mt.renda)}</b></div>` : ''}
        <div class="it"><div class="grow">Composição</div><span>${invs.length ? invs.map(i => esc(i.nome)).join(', ') : ''}${mt.saldo ? (invs.length ? ' + ' : '') + 'saldo manual ' + fmtR(mt.saldo) : ''}${!invs.length && !mt.saldo ? '<span class="muted">vincule investimentos</span>' : ''}</span></div>
      </div></div>`; }).join('') : '<div class="card vazio" style="grid-column:1/-1">Crie metas para viagens, aposentadoria e reserva de emergência. O programa calcula quanto guardar por mês.</div>'}</div>`;
  ligarTopo(el);
  el.querySelector('#bnova').onclick = () => editarMeta();
  const bs = el.querySelector('#bsug'); if (bs) bs.onclick = () => editarMeta(null, {tipo: 'emergencia', nome: 'Reserva de emergência', alvo: Math.round(med * 6 / 100) * 100, rent: 0, dono: 'casal'});
  el.querySelectorAll('[data-ed]').forEach(b => b.onclick = () => editarMeta(S.metas.find(m => m.id === b.dataset.ed)));
}
function editarMeta(mt, pre) {
  const novo = !mt; mt = mt || pre || {tipo: 'viagem', rent: 4, dono: 'casal'};
  const box = formModal(novo ? 'Nova meta' : 'Editar meta', [
    {k: 'nome', label: 'Nome', req: true, ph: 'Ex.: Viagem Europa jul/2028'},
    {k: 'tipo', label: 'Tipo', type: 'select', options: Object.entries(TIPO_META), half: true},
    ...(S.pessoas.length > 1 ? [{k: 'dono', label: 'De quem', type: 'select', options: optPessoas(), half: true}] : []),
    {k: 'alvo', label: 'Valor alvo (R$)', type: 'money', req: true, half: true},
    {k: 'data', label: 'Data alvo', type: 'month', half: true},
    {k: 'saldo', label: 'Já guardado fora dos investimentos (R$)', type: 'money', half: true, help: 'Investimentos vinculados somam automaticamente.'},
    {k: 'rent', label: 'Rentabilidade real esperada (% a.a.)', type: 'number', step: '0.1', half: true, help: 'Acima da inflação. Ex.: 4.'},
    {k: 'idade', label: 'Aposentadoria: sua idade hoje', type: 'number', half: true},
    {k: 'idadeAlvo', label: 'Idade para se aposentar', type: 'number', half: true},
    {k: 'renda', label: 'Renda mensal desejada (R$, valores de hoje)', type: 'money', help: 'Preenchendo, o alvo é sugerido pela regra dos 4% (renda × 12 ÷ 4%) e a data pela idade.'},
    CAMPO_PRIV(),
  ], {...mt, data: mt.data ? mt.data.slice(0, 7) : ''}, v => {
    if (v.tipo === 'aposentadoria' && v.renda && !v.alvo) v.alvo = v.renda * 12 / 0.04;
    if (v.tipo === 'aposentadoria' && v.idade && v.idadeAlvo && !v.data) v.data = addMes(mesAtual(), (v.idadeAlvo - v.idade) * 12);
    Object.assign(mt, v); if (novo) { mt.id = uid(); S.metas.push(mt); }
  }, {aoExcluir: novo ? null : () => { S.metas = S.metas.filter(x => x.id !== mt.id); S.investimentos.forEach(i => { if (i.meta === mt.id) i.meta = ''; }); }});
  // sugestão automática de alvo/data para aposentadoria
  const sync = () => {
    const t = box.querySelector('#f_tipo').value; ['idade', 'idadeAlvo', 'renda'].forEach(k => box.querySelector('#f_' + k).closest('.fld').classList.toggle('hidden', t !== 'aposentadoria'));
  };
  box.querySelector('#f_tipo').onchange = sync; sync();
  const sug = () => {
    if (box.querySelector('#f_tipo').value !== 'aposentadoria') return;
    const r = parseBR(box.querySelector('#f_renda').value), id = +box.querySelector('#f_idade').value, ia = +box.querySelector('#f_idadeAlvo').value;
    if (r) box.querySelector('#f_alvo').value = fmtN(r * 12 / 0.04, 2);
    if (id && ia > id) box.querySelector('#f_data').value = addMes(mesAtual(), (ia - id) * 12);
  };
  ['#f_renda', '#f_idade', '#f_idadeAlvo'].forEach(s => box.querySelector(s).onchange = sug);
}

/* =====================================================================
   CONFIGURAÇÕES
   ===================================================================== */
async function vConfig(el) {
  const usuarios = Object.entries(COFRE || {});
  const fator = (auth.currentUser && multiFactor(auth.currentUser).enrolledFactors) || [];
  el.innerHTML = topo('Configurações', {pessoa: false}) + `
  <div class="grid g2">
    <div class="card"><h3>Usuários</h3>
      <div class="list">${usuarios.map(([u, d]) => `<div class="it"><div class="grow"><b>${esc(d.nome)}</b>${u === USER.uid ? ' <span class="tag dark">você</span>' : ''}<div class="small muted">pessoa: ${esc(pessoa(d.pessoa)?.nome || '—')} · desde ${fmtData((d.criadoEm || '').slice(0, 10))}</div></div>${u === USER.uid ? '' : `<button class="btn sm ghost" data-rmu="${u}" style="color:var(--vermelho)">Remover acesso</button>`}</div>`).join('')}</div>
      <button class="btn" id="bconv" style="margin-top:10px">+ Convidar pessoa</button>
      <div class="small muted" style="margin-top:8px">O convite gera um código de uso único, válido por 48 h. Passe o código pessoalmente ou por telefone. O e-mail da pessoa também precisa estar liberado no Firebase.</div>
      <h3 style="margin-top:20px">Pessoas da família</h3>
      <div class="list">${S.pessoas.map(p => `<div class="it"><div class="grow">${esc(p.nome)}</div><button class="btn sm ghost" data-rp="${p.id}">Renomear</button></div>`).join('')}</div>
      <button class="btn sm" id="baddp" style="margin-top:8px">+ Adicionar pessoa (sem login)</button>
    </div>
    <div class="card"><h3>Minha segurança</h3>
      <div class="list">
        <div class="it"><div class="grow"><b>Verificação em duas etapas</b><div class="small muted">${fator.length ? 'Ativa (app autenticador)' : 'Desativada — recomendado ativar'}</div></div>${fator.length ? '<span class="tag ok">ativa</span>' : '<button class="btn sm pri" id="b2fa">Ativar</button>'}</div>
        <div class="it"><div class="grow"><b>Senha do cofre</b><div class="small muted">Decifra os dados no aparelho. Nunca sai dele.</div></div><button class="btn sm" id="btrsen">Trocar</button></div>
        <div class="it"><div class="grow"><b>Senha de acesso</b><div class="small muted">${esc(USER.email)}</div></div><button class="btn sm" id="btracs">Trocar</button></div>
        <div class="it"><div class="grow"><b>Bloquear após inatividade</b></div><input class="in" type="number" id="cblq" min="1" max="120" value="${S.config.bloqueioMin || 10}" style="max-width:90px"> <span class="small muted">min</span></div>
      </div>
      <h3 style="margin-top:20px">Acessos recentes</h3><div id="acessos" class="small muted">Carregando…</div>
    </div>
  </div>
  <div class="grid g2" style="margin-top:16px">
    <div class="card"><h3>Sincronização com os bancos (Open Finance)</h3><div id="syncst" class="small muted">Carregando…</div>
      ${Object.keys(S.config.mapaPluggy || {}).length ? `<h3 style="margin-top:16px">Contas conectadas</h3><table class="t"><tbody>${Object.entries(S.config.mapaPluggy).map(([pid, cid]) => `<tr><td>${esc(conta(cid)?.nome || '(removida)')}</td><td class="small muted">${esc(conta(cid)?.banco || '')}</td><td class="r small">${conta(cid)?.saldoBanco ? fmtR(conta(cid).saldoBanco.valor) : ''}</td></tr>`).join('')}</tbody></table>` : ''}
      ${(S.config.pluggy?.itens || []).length ? `<h3 style="margin-top:16px">Autorizações</h3>${S.config.pluggy.itens.map(i => { const d = i.consentExpira ? diasEntre(hoje(), i.consentExpira.slice(0, 10)) : null; return `<div class="it" style="display:flex;gap:8px;padding:4px 0"><span class="grow">${esc(i.banco || i.id)}</span><span class="tag ${i.status === 'UPDATED' ? 'ok' : 'warn'}">${esc(i.status || '')}</span>${d != null ? `<span class="tag ${d < 30 ? 'red' : ''}">expira ${fmtData(i.consentExpira.slice(0, 10))}</span>` : ''}</div>`; }).join('')}` : ''}
    </div>
    <div class="card"><h3>Backup</h3>
      <p class="small">Os dados ficam cifrados no Firebase. Mesmo assim, exporte um backup de vez em quando (ele também abre no Portafoglio offline). Itens marcados como privados não entram no backup.</p>
      <div class="ctrl"><button class="btn pri" id="bexp">Exportar backup cifrado</button></div>
      <div class="small muted" style="margin-top:8px">Último backup: ${S.config.ultimoBackup ? fmtData(S.config.ultimoBackup.slice(0, 10)) : 'nunca'}</div>
    </div>
  </div>
  <div class="grid g2" style="margin-top:16px">
    <div class="card"><h3>Categorias <span class="x"><button class="btn sm" id="bnc">+ Nova</button></span></h3>
      <div class="small muted" style="margin-bottom:8px">Limite mensal opcional para acompanhar o orçamento. <b>Neutro</b> não conta como gasto (pagamento de fatura, transferências); <b>Reserva</b> conta como dinheiro guardado.</div>
      <table class="t"><thead><tr><th>Categoria</th><th>Tipo</th><th class="r">Limite/mês</th><th></th></tr></thead><tbody>
      ${S.categorias.map(c => `<tr><td><span class="dot" style="background:${c.cor}"></span>${esc(c.nome)}</td><td class="small">${c.tipo}</td><td class="r">${c.limite ? fmtR(c.limite) : '·'}</td><td class="r"><button class="btn sm ghost" data-ec="${c.id}">Editar</button></td></tr>`).join('')}</tbody></table>
    </div>
    <div class="card"><h3>Regras de categorização <span class="x"><button class="btn sm" id="bnr">+ Nova</button></span></h3>
      <div class="small muted" style="margin-bottom:8px">Se a descrição contém o termo, recebe a categoria. Termos mais longos têm prioridade. Valem para importação e para o que chega dos bancos.</div>
      <div class="tw" style="max-height:420px"><table class="t"><thead><tr><th>Termo</th><th>Categoria</th><th></th></tr></thead><tbody>
      ${[...S.regras].sort((a, b) => a.termo.localeCompare(b.termo)).map(r => `<tr><td><code>${esc(r.termo)}</code></td><td class="small">${esc(cat(r.cat).nome)}</td><td class="r"><button class="btn sm ghost" data-er="${r.id}">Editar</button></td></tr>`).join('')}</tbody></table></div>
      <button class="btn sm" id="breap" style="margin-top:10px">Reaplicar regras nos lançamentos sem categoria</button>
    </div>
  </div>
  <div class="card" style="margin-top:16px"><h3>Mensagem de cobrança (WhatsApp)</h3>
    <textarea class="in" id="cmsg" style="min-height:110px">${esc(S.config.msgWhats)}</textarea><div class="small muted">Use {nome}, {mes} e {lista}.</div>
  </div>`;
  el.querySelector('#cblq').onchange = e => { S.config.bloqueioMin = Math.max(1, +e.target.value || 10); salvar(); };
  el.querySelector('#cmsg').onchange = e => { S.config.msgWhats = e.target.value; salvar(); toast('Mensagem salva'); };
  el.querySelector('#bexp').onclick = exportarBackup;
  el.querySelector('#btrsen').onclick = trocarSenhaCofre;
  el.querySelector('#btracs').onclick = trocarSenhaAcesso;
  const b2 = el.querySelector('#b2fa'); if (b2) b2.onclick = ativar2FA;
  el.querySelector('#bconv').onclick = convidar;
  el.querySelector('#baddp').onclick = () => formModal('Adicionar pessoa', [{k: 'nome', label: 'Nome', req: true}], {}, v => { S.pessoas.push({id: uid(), nome: v.nome, o: S.pessoas.length}); });
  el.querySelectorAll('[data-rp]').forEach(b => b.onclick = () => { const p = pessoa(b.dataset.rp); formModal('Renomear', [{k: 'nome', label: 'Nome', req: true}], p, v => { p.nome = v.nome; }); });
  el.querySelectorAll('[data-rmu]').forEach(b => b.onclick = async () => {
    const u = b.dataset.rmu; if (!confirm(`Remover o acesso de ${COFRE[u].nome}? Os dados compartilhados continuam; a chave dele(a) é apagada.\n\nPara bloquear de vez, tire também o e-mail da lista de membros no Firebase.`)) return;
    await set(R('cofre/usuarios/' + u), null); delete COFRE[u]; toast('Acesso removido'); render();
  });
  el.querySelector('#bnc').onclick = () => editarCat();
  el.querySelectorAll('[data-ec]').forEach(b => b.onclick = () => editarCat(S.categorias.find(c => c.id === b.dataset.ec)));
  el.querySelector('#bnr').onclick = () => editarRegra();
  el.querySelectorAll('[data-er]').forEach(b => b.onclick = () => editarRegra(S.regras.find(r => r.id === b.dataset.er)));
  el.querySelector('#breap').onclick = () => { let n = 0; for (const l of S.lancamentos) if (!l.cat) { const c = aplicarRegras(l.desc); if (c) { l.cat = c; n++; } } salvar(); toast(n + ' lançamento(s) classificados'); };
  // acessos
  try {
    const linhas = [];
    for (const [u, d] of usuarios) {
      const a = (await get(query(R('acessos/' + u), limitToLast(6)))).val() || {};
      Object.values(a).forEach(x => linhas.push({...x, nome: d.nome}));
    }
    linhas.sort((a, b) => b.quando.localeCompare(a.quando));
    const ac = el.querySelector('#acessos');
    if (ac) ac.innerHTML = linhas.length ? '<table class="t"><tbody>' + linhas.slice(0, 10).map(x => `<tr><td>${esc(x.nome)}</td><td>${esc(x.disp)}</td><td class="r">${new Date(x.quando).toLocaleString('pt-BR', {dateStyle: 'short', timeStyle: 'short'})}</td></tr>`).join('') + '</tbody></table>' : 'Nenhum registro.';
  } catch (e) {}
  try {
    const st = (await get(R('sync/status'))).val(); const sx = el.querySelector('#syncst');
    if (sx) sx.innerHTML = st ? `Última execução do robô: <b>${new Date(st.quando).toLocaleString('pt-BR', {dateStyle: 'short', timeStyle: 'short'})}</b> · ${st.ok ? '<span class="tag ok">ok</span>' : '<span class="tag red">erro</span>'} ${esc(st.msg || '')}<br>Pacotes aguardando: processados automaticamente ao abrir o app.`
      : 'Ainda não configurada. Siga o guia de instalação, parte "Sincronização com os bancos".';
  } catch (e) {}
}
function editarCat(c) {
  const novo = !c; c = c || {tipo: 'despesa', cor: '#6b6b73', limite: 0};
  formModal(novo ? 'Nova categoria' : 'Editar categoria', [
    {k: 'nome', label: 'Nome', req: true},
    {k: 'tipo', label: 'Tipo', type: 'select', options: [['despesa', 'Despesa'], ['receita', 'Receita'], ['reserva', 'Reserva (dinheiro guardado)'], ['neutro', 'Neutro (não conta)']], half: true},
    {k: 'cor', label: 'Cor', type: 'color', half: true},
    {k: 'limite', label: 'Limite mensal (R$) — opcional', type: 'money'},
  ], c, v => { Object.assign(c, v); if (novo) { c.id = uid(); c.o = S.categorias.length; S.categorias.push(c); } },
  {aoExcluir: novo ? null : () => { S.categorias = S.categorias.filter(x => x.id !== c.id); S.lancamentos.forEach(l => { if (l.cat === c.id) l.cat = ''; }); S.regras = S.regras.filter(r => r.cat !== c.id); }});
}
function editarRegra(r) {
  const novo = !r; r = r || {};
  formModal(novo ? 'Nova regra' : 'Editar regra', [
    {k: 'termo', label: 'Se a descrição contiver', req: true, ph: 'Ex.: ZONA SUL'},
    {k: 'cat', label: 'Classificar como', type: 'select', options: optCats(), req: true},
  ], r, v => { Object.assign(r, v); if (novo) { r.id = uid(); S.regras.push(r); } },
  {aoExcluir: novo ? null : () => { S.regras = S.regras.filter(x => x.id !== r.id); }});
}
function convidar() {
  const livres = S.pessoas.filter(p => !Object.values(COFRE).some(u => u.pessoa === p.id));
  const box = modal(`<h3>Convidar pessoa</h3><div class="small muted">Ela vai criar o próprio login (com o e-mail dela) e, na primeira entrada, digitar este código.</div><div class="filete"></div>
    <div class="fld"><label>Nome</label><input class="in" id="cn" value="${esc(livres[0]?.nome || '')}"></div>
    <div class="fld"><label>Vincular à pessoa</label><select class="in" id="cp">${livres.map(p => `<option value="${p.id}">${esc(p.nome)}</option>`).join('')}<option value="_nova">Criar nova pessoa com este nome</option></select></div>
    <div id="cres"></div><div class="erro" id="ce"></div>
    <div class="acts"><button class="btn" id="cc">Fechar</button><button class="btn pri" id="co">Gerar código</button></div>`);
  box.querySelector('#cc').onclick = fecharModal;
  box.querySelector('#co').onclick = async () => {
    const nome = box.querySelector('#cn').value.trim(); if (!nome) return box.querySelector('#ce').textContent = 'Informe o nome.';
    let pid = box.querySelector('#cp').value; if (pid === '_nova') { pid = uid(); S.pessoas.push({id: pid, nome, o: S.pessoas.length}); salvar(); }
    box.querySelector('#ce').textContent = 'Gerando…';
    const code = gerarCodigo(); const id = await hashCodigo(code);
    await set(R('convites/' + id), {nome, pessoa: pid, por: USER.nome, expira: Date.now() + 48 * 3600 * 1000, ...(await embrulhar(RAW, code))});
    box.querySelector('#ce').textContent = '';
    box.querySelector('#cres').innerHTML = `<div class="alert"><div class="tx"><b style="font-size:22px;letter-spacing:2px;font-family:ui-monospace,Menlo,monospace">${code}</b><span class="small muted">Válido por 48 h, uso único. Não envie junto com a senha.</span></div></div>`;
    box.querySelector('#co').classList.add('hidden');
  };
}
function trocarSenhaCofre() {
  const box = modal(`<h3>Trocar senha do cofre</h3><div class="filete"></div>
    <div class="fld"><label>Senha atual do cofre</label><input class="in" type="password" id="sa"></div>
    <div class="fld"><label>Nova senha (mín. 10)</label><input class="in" type="password" id="sn"></div>
    <div class="fld"><label>Repita</label><input class="in" type="password" id="sn2"></div><div class="erro" id="se"></div>
    <div class="acts"><button class="btn" id="sc">Cancelar</button><button class="btn pri" id="so">Trocar</button></div>`);
  box.querySelector('#sc').onclick = fecharModal;
  box.querySelector('#so').onclick = async () => {
    const e = box.querySelector('#se'); const a = box.querySelector('#sa').value, n = box.querySelector('#sn').value;
    const fm = senhaForteMsg(n); if (fm) return e.textContent = fm;
    if (n !== box.querySelector('#sn2').value) return e.textContent = 'As senhas não conferem.';
    try { await desembrulhar(COFRE[USER.uid], a); } catch (x) { return e.textContent = 'Senha atual incorreta.'; }
    e.textContent = 'Gerando…';
    const w = await embrulhar(RAW, n), wp = await embrulhar(PRAW, n);
    const novo = {...COFRE[USER.uid], ...w};
    await update(ref(db, 'pf'), {['cofre/usuarios/' + USER.uid]: novo, [`privado/${USER.uid}/chave`]: wp});
    COFRE[USER.uid] = novo; fecharModal(); toast('Senha do cofre alterada');
  };
}
function trocarSenhaAcesso() {
  const box = modal(`<h3>Trocar senha de acesso</h3><div class="filete"></div>
    <div class="fld"><label>Senha de acesso atual</label><input class="in" type="password" id="sa"></div>
    <div class="fld"><label>Nova senha (mín. 10)</label><input class="in" type="password" id="sn"></div><div class="erro" id="se"></div>
    <div class="acts"><button class="btn" id="sc">Cancelar</button><button class="btn pri" id="so">Trocar</button></div>`);
  box.querySelector('#sc').onclick = fecharModal;
  box.querySelector('#so').onclick = async () => {
    const e = box.querySelector('#se'), n = box.querySelector('#sn').value; if (n.length < 10) return e.textContent = 'Mínimo de 10 caracteres.';
    try { await reauthenticateWithCredential(auth.currentUser, EmailAuthProvider.credential(USER.email, box.querySelector('#sa').value)); await updatePassword(auth.currentUser, n); fecharModal(); toast('Senha de acesso alterada. Outros aparelhos precisarão entrar de novo.'); }
    catch (x) { if (x.code === 'auth/multi-factor-auth-required') return e.textContent = 'Saia e entre de novo (com o código do autenticador) e tente outra vez.'; e.textContent = erroAuth(x); }
  };
}
function ativar2FA() {
  const box = modal(`<h3>Ativar verificação em duas etapas</h3><div class="small muted">Você vai precisar de um app autenticador no celular (Google Authenticator, Microsoft Authenticator ou similar).</div><div class="filete"></div>
    <div id="p1"><div class="fld"><label>Confirme sua senha de acesso</label><input class="in" type="password" id="ap"></div><div class="acts"><button class="btn" id="ac">Cancelar</button><button class="btn pri" id="ao">Continuar</button></div></div>
    <div id="p2" class="hidden"><p class="small">1. No app autenticador, adicione uma conta lendo o QR code abaixo (ou digitando a chave).</p><div id="qr" style="text-align:center"></div>
      <div class="small" style="text-align:center;margin:6px 0 12px">Chave: <code id="key" style="word-break:break-all"></code></div>
      <div class="fld"><label>2. Digite o código de 6 dígitos que aparece no app</label><input class="in" id="acod" inputmode="numeric" maxlength="6" style="font-size:20px;letter-spacing:5px;text-align:center"></div>
      <div class="acts"><button class="btn pri" id="aok">Ativar</button></div></div>
    <div class="erro" id="ae"></div>`);
  box.querySelector('#ac').onclick = fecharModal;
  let secret = null;
  box.querySelector('#ao').onclick = async () => {
    const e = box.querySelector('#ae'); e.textContent = '';
    try {
      await reauthenticateWithCredential(auth.currentUser, EmailAuthProvider.credential(USER.email, box.querySelector('#ap').value));
      const ses = await multiFactor(auth.currentUser).getSession();
      secret = await TotpMultiFactorGenerator.generateSecret(ses);
      const url = secret.generateQrCodeUrl(USER.email, 'Portafoglio');
      const q = qrcode(0, 'M'); q.addData(url); q.make(); box.querySelector('#qr').innerHTML = q.createSvgTag({cellSize: 5, margin: 2});
      box.querySelector('#key').textContent = secret.secretKey;
      box.querySelector('#p1').classList.add('hidden'); box.querySelector('#p2').classList.remove('hidden'); box.querySelector('#acod').focus();
    } catch (x) {
      if (/operation-not-allowed|admin-restricted|unsupported/.test(x.code || '')) e.textContent = 'A verificação em duas etapas ainda não foi habilitada no projeto Firebase (veja o guia, passo "Ativar 2FA").';
      else e.textContent = erroAuth(x);
    }
  };
  box.querySelector('#aok').onclick = async () => {
    const e = box.querySelector('#ae');
    try { await multiFactor(auth.currentUser).enroll(TotpMultiFactorGenerator.assertionForEnrollment(secret, box.querySelector('#acod').value.trim()), 'Autenticador'); fecharModal(); toast('Verificação em duas etapas ativada.'); render(); }
    catch (x) { e.textContent = erroAuth(x); }
  };
}
async function exportarBackup() {
  await salvar(true);
  S.config.ultimoBackup = new Date().toISOString(); await salvar(true);
  const pub = JSON.parse(JSON.stringify(S));
  COLS_PRIV.forEach(c => pub[c] = (pub[c] || []).filter(x => !x.privado));
  delete pub.chavesSync;
  const usuarios = Object.values(COFRE).map(u => ({id: uid(), nome: u.nome, pessoa: u.pessoa, salt: u.salt, iv: u.iv, iter: u.iter, chave: u.chave}));
  const c = await cifrar(CHAVE, pub);
  const env = {app: 'familia-financas', formato: 2, origem: 'web', usuarios, ...c, salvoEm: new Date().toISOString()};
  const blob = new Blob([JSON.stringify(env)], {type: 'application/octet-stream'});
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = `portafoglio_${hoje()}.portafoglio`; a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000); toast('Backup exportado (cifrado).'); render();
}

/* =====================================================================
   LANÇAMENTO RÁPIDO (celular)
   ===================================================================== */
function lancamentoRapido() {
  const usadas = {}; S.lancamentos.slice(-300).forEach(l => { if (l.cat && l.valor < 0) usadas[l.cat] = (usadas[l.cat] || 0) + 1; });
  const top = Object.entries(usadas).sort((a, b) => b[1] - a[1]).slice(0, 8).map(([id]) => id);
  const cats = top.length ? top : S.categorias.filter(c => c.tipo === 'despesa').slice(0, 8).map(c => c.id);
  const contas = S.contas.filter(c => passaPessoa(c.dono));
  let catSel = '', tipo = 'saida';
  const box = modal(`<h3>Lançamento rápido</h3><div class="filete"></div>
    <div class="seg" id="qt" style="margin-bottom:10px"><button data-t="saida" class="on">Paguei / gastei</button><button data-t="entrada">Recebi</button></div>
    <input class="in" id="qv" inputmode="decimal" placeholder="R$ 0,00" style="font-size:28px;font-weight:700;text-align:center;padding:12px">
    <div class="fld" style="margin-top:10px"><input class="in" id="qd" placeholder="Descrição (ex.: Pix para o pintor)"></div>
    <div id="qc" style="display:flex;flex-wrap:wrap;gap:6px;margin-bottom:10px">${cats.map(id => `<button class="btn sm" data-c="${id}"><span class="dot" style="background:${cat(id).cor}"></span>${esc(cat(id).nome)}</button>`).join('')}<select class="in" id="qcat" style="max-width:180px;padding:4px 8px;font-size:12px"><option value="">outra…</option>${optCats().map(([a, b]) => `<option value="${a}">${esc(b)}</option>`).join('')}</select></div>
    <div class="frow"><div class="fld"><label>Conta / cartão</label><select class="in" id="qconta"><option value="">—</option>${contas.map(c => `<option value="${c.id}">${esc(c.nome)}</option>`).join('')}</select></div>
    <div class="fld"><label>Data</label><input class="in" type="date" id="qdt" value="${hoje()}"></div></div>
    <label class="chk small"><input type="file" id="qf" accept=".pdf" class="hidden"><a href="#" id="qcomp">Preencher a partir do comprovante (PDF)</a></label>
    <div class="erro" id="qe"></div>
    <div class="acts"><button class="btn" id="qx">Cancelar</button><button class="btn red" id="qok" style="padding:10px 22px">Salvar</button></div>`);
  try { const ult = localStorage.getItem('pf.ultimaConta'); if (ult && contas.some(c => c.id === ult)) box.querySelector('#qconta').value = ult; } catch (e) {}
  box.querySelectorAll('#qt button').forEach(b => b.onclick = () => { tipo = b.dataset.t; box.querySelectorAll('#qt button').forEach(x => x.classList.toggle('on', x === b)); });
  const marcar = () => box.querySelectorAll('#qc [data-c]').forEach(b => b.classList.toggle('pri', b.dataset.c === catSel));
  box.querySelectorAll('#qc [data-c]').forEach(b => b.onclick = () => { catSel = b.dataset.c; box.querySelector('#qcat').value = ''; marcar(); });
  box.querySelector('#qcat').onchange = e => { catSel = e.target.value; marcar(); };
  box.querySelector('#qd').onchange = e => { if (!catSel) { const c = aplicarRegras(e.target.value); if (c) { catSel = c; if (!box.querySelector(`[data-c="${c}"]`)) box.querySelector('#qcat').value = c; marcar(); } } };
  box.querySelector('#qx').onclick = fecharModal;
  box.querySelector('#qcomp').onclick = e => { e.preventDefault(); box.querySelector('#qf').click(); };
  box.querySelector('#qf').onchange = async e => {
    const f = e.target.files[0]; if (!f) return; const qe = box.querySelector('#qe'); qe.style.color = 'var(--cinza4)'; qe.textContent = 'Lendo comprovante…';
    try {
      const linhas = (await textoPdf(await f.arrayBuffer())).flat(); const c = lerComprovante(linhas);
      if (c.valor) box.querySelector('#qv').value = fmtN(c.valor, 2);
      if (c.data) box.querySelector('#qdt').value = c.data;
      if (c.para) { box.querySelector('#qd').value = (c.pix ? 'Pix ' : '') + c.para; box.querySelector('#qd').dispatchEvent(new Event('change')); }
      qe.textContent = c.valor ? 'Confira os dados e salve.' : 'Não encontrei o valor; preencha manualmente.';
    } catch (x) { qe.style.color = ''; qe.textContent = 'Não consegui ler: ' + (x.message || x); }
  };
  box.querySelector('#qok').onclick = () => {
    const v = Math.abs(parseBR(box.querySelector('#qv').value)); const qe = box.querySelector('#qe');
    if (!v) return qe.textContent = 'Informe o valor.';
    const desc = box.querySelector('#qd').value.trim() || cat(catSel).nome || 'Lançamento';
    const data = box.querySelector('#qdt').value || hoje(); const contaId = box.querySelector('#qconta').value;
    const c = conta(contaId);
    S.lancamentos.push({id: uid(), data, mesRef: c?.tipo === 'cartao' ? mesFatura(c, data) : data.slice(0, 7), desc, valor: tipo === 'saida' ? -v : v, cat: catSel, conta: contaId, origem: 'manual', autor: USER.nome});
    try { localStorage.setItem('pf.ultimaConta', contaId); } catch (e) {}
    salvar(); fecharModal(); toast('Lançado: ' + fmtR(tipo === 'saida' ? -v : v)); render();
  };
  setTimeout(() => box.querySelector('#qv').focus(), 60);
}
function lerComprovante(linhas) {
  const txt = linhas.join('\n'); const out = {};
  const vm = txt.match(/(?:valor(?: pago| da transfer[êe]ncia| do pix)?|total)[^\d\n]{0,25}R?\$?\s*(\d{1,3}(?:\.\d{3})*,\d{2})/i) || txt.match(/R\$\s*(\d{1,3}(?:\.\d{3})*,\d{2})/);
  if (vm) out.valor = parseBR(vm[1]);
  const dm = txt.match(/(\d{2})\/(\d{2})\/(\d{4})/) || txt.match(/(\d{2})\s+(?:de\s+)?(jan|fev|mar|abr|mai|jun|jul|ago|set|out|nov|dez)[a-zç]*\.?\s+(?:de\s+)?(\d{4})/i);
  if (dm) { const mm = isNaN(+dm[2]) ? MESES_AB.indexOf(dm[2].slice(0, 3).toUpperCase()) + 1 : +dm[2]; out.data = dm[3] + '-' + String(mm).padStart(2, '0') + '-' + dm[1]; }
  out.pix = /\bpix\b/i.test(txt);
  for (let i = 0; i < linhas.length; i++) {
    const l = linhas[i];
    const m = l.match(/^\s*(?:para|destino|destinat[áa]rio|favorecido|recebedor|quem recebeu|nome do recebedor|pago a)\s*:?\s*(.*)$/i);
    if (m) { let n = m[1].trim(); if (!n || n.length < 3) n = (linhas[i + 1] || '').trim(); if (n && !/^(nome|cpf|cnpj|institui)/i.test(n)) { out.para = n.replace(/\s{2,}.*/, '').slice(0, 60); break; } }
    const m2 = l.match(/^\s*nome\s*:?\s*(.+)$/i); if (m2 && !out.para && i > 0 && /destino|para|recebe|favorecid/i.test(linhas.slice(Math.max(0, i - 3), i).join(' '))) { out.para = m2[1].trim().slice(0, 60); break; }
  }
  return out;
}

/* ---------------- início ---------------- */
onAuthStateChanged(auth, u => {
  if (S && u && USER && u.uid === USER.uid) return; // já aberto
  if (!u) { if (!$('#lock').classList.contains('hidden') && $('#le')) return; telaLogin(); }
  else posLogin(u);
});
if ('serviceWorker' in navigator && location.protocol === 'https:') navigator.serviceWorker.register('sw.js').catch(() => {});
