module

public import Certificates.Data.CFSGNative.ExcCensus.Tables

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

@[expose] def dig (c k : Nat) : Nat := c / 3 ^ k % 3

@[expose] def ofDigits (d : Nat) (f : Nat → Nat) : Nat :=
  Nat.fold d (fun k _ acc => acc + f k % 3 * 3 ^ k) 0

@[expose] def combN (d cv cy a b : Nat) : Nat :=
  ofDigits d fun k => a * dig cv k + b * dig cy k

@[expose] def pivN (d c : Nat) : Nat :=
  ((List.range d).find? fun k => dig c k != 0).getD d

@[expose] def canonN (d cv cy : Nat) : Bool :=
  decide (cy < 3 ^ d) && dig cy (pivN d cv) == 0 && decide (pivN d cy < d) &&
    dig cy (pivN d cy) == 1

@[expose] def maskN (r : Nat) (p : Nat → Bool) : Nat :=
  Nat.fold r (fun t _ acc => if p t then acc ||| 1 <<< t else acc) 0

@[expose] def cardN (r c : Nat) : Nat := (List.range r).countP fun t => c.testBit t

@[expose] def subN (c c' : Nat) : Bool := c &&& c' == c

@[expose] def trunc (r c : Nat) : Nat := c &&& (2 ^ r - 1)

@[expose] def fN (m : Fin 6) (i k : Nat) : Int := ((tabF m).getD i []).getD k 0

@[expose] def hN (m : Fin 6) (i k : Nat) : Int := ((tabH m).getD i []).getD k 0

@[expose] def pairN (m : Fin 6) (i j : Nat) : Int :=
  if m.val = 3 then Nat.fold 6 (fun k _ s => s + fN 2 i k * hN 2 j k) 0
  else Nat.fold (dim m) (fun k _ s => s + fN m i k * hN m j k) 0

structure Tabs where
  f : Array (Array Int)
  h : Array (Array Int)
  pair : Array (Array Int)
  adj : Array Nat
  zm : Array Nat
  rt : Array (Array Nat)
  deriving Inhabited

@[expose] def evA (T : Tabs) (d t c : Nat) : Int :=
  Nat.fold d (fun k _ s => s + T.f[t]![k]! * (dig c k : Int)) 0 % 3

@[expose] def zmA (T : Tabs) (d r c : Nat) : Nat := maskN r fun t => evA T d t c == 0

@[expose] def adjA (T : Tabs) (r i : Nat) : Nat :=
  maskN r fun j => T.pair[i]![j]! != 0 || T.pair[j]![i]! != 0

@[expose] def rtEq (T : Tabs) (d t' u t : Nat) (ε : Int) : Bool :=
  Nat.all d fun k _ =>
    (T.f[t']![k]! - ε * (T.f[t]![k]! - T.pair[t]![u]! * T.f[u]![k]!)) % 3 == 0 &&
      (T.h[t']![k]! - ε * (T.h[t]![k]! - T.pair[u]![t]! * T.h[u]![k]!)) % 3 == 0

@[expose] def tabsOK (m : Fin 6) (T : Tabs) : Bool :=
  let d := dim m
  let r := nroots m
  T.f.size == r && T.h.size == r && T.pair.size == r && T.adj.size == r &&
    T.zm.size == 3 ^ d && T.rt.size == r &&
    (Nat.all r fun i _ => Nat.all d fun k _ =>
      T.f[i]![k]! == fN m i k && T.h[i]![k]! == hN m i k) &&
    (Nat.all r fun i _ => Nat.all r fun j _ => T.pair[i]![j]! == pairN m i j) &&
    (Nat.all r fun i _ => T.adj[i]! == adjA T r i) &&
    (Nat.all (3 ^ d) fun c _ => T.zm[c]! == zmA T d r c) &&
    (Nat.all r fun u _ => Nat.all r fun t _ =>
      decide (T.rt[u]![t]! < r) &&
        (rtEq T d T.rt[u]![t]! u t 1 || rtEq T d T.rt[u]![t]! u t (-1)))

@[expose] def closedOK (T : Tabs) (r c S : Nat) : Bool :=
  let c' := trunc r c
  let S' := S &&& c'
  S' != 0 && S' != c' && Nat.all r fun t _ => !S'.testBit t || subN (T.adj[t]! &&& c') S'

@[expose] def growN (T : Tabs) (r c S : Nat) : Nat :=
  Nat.fold r (fun t _ acc => if S.testBit t then acc ||| (T.adj[t]! &&& c) else acc) S

@[expose] def lowN (r c : Nat) : Nat := ((List.range r).find? fun t => c.testBit t).getD r

@[expose] def connN (T : Tabs) (r c : Nat) : Bool :=
  let c' := trunc r c
  decide (lowN r c' < r) && Nat.repeat (growN T r c') r (1 <<< lowN r c') == c'

@[expose] def phiN (T : Tabs) (d p : Nat) (rows : List Nat) (i j : Nat) : Int :=
  if i + 1 < d then T.f[rows.getD i 0]![j]! else if j = p then 1 else 0

@[expose] def lineOK (T : Tabs) (d r : Nat) (rows : List Nat) (cz : Nat)
    (B : Array (Array Int)) : Bool :=
  let p := pivN d cz
  decide (cz < 3 ^ d) && decide (p < d) && rows.length + 1 == d &&
    rows.all (fun t => decide (t < r) && (T.zm[cz]!).testBit t) &&
    Nat.all d fun i _ => Nat.all d fun j _ =>
      (Nat.fold d (fun k _ s => s + B[i]![k]! * phiN T d p rows k j) 0 -
        (if i = j then 1 else 0)) % 3 == 0

@[expose] def inOK (T : Tabs) (d r c : Nat) (coef : List (Nat × Nat)) (cv : Nat) : Bool :=
  coef.all (fun e => decide (e.1 < r) && c.testBit e.1) &&
    Nat.all d fun k _ =>
      (coef.foldl (fun s e => s + (e.2 : Int) * T.h[e.1]![k]!) 0 - (dig cv k : Int)) % 3 == 0

@[expose] def outOK (T : Tabs) (d r c φ cv : Nat) : Bool :=
  (Nat.all r fun t _ => !c.testBit t ||
    Nat.fold d (fun k _ s => s + (dig φ k : Int) * T.h[t]![k]!) 0 % 3 == 0) &&
    Nat.fold d (fun k _ s => s + (dig φ k : Int) * (dig cv k : Int)) 0 % 3 != 0

@[expose] def orthN (T : Tabs) (r c : Nat) : Nat :=
  Nat.fold r (fun i _ acc => if c.testBit i then
    Nat.fold r (fun j _ acc' => if c.testBit j && T.pair[i]![j]! == 0 then acc' + 1 else acc')
      acc else acc) 0

@[expose] def longN (r c : Nat) : Nat :=
  (List.range r).countP fun t => c.testBit t && tabFix1.getD t false

@[expose] def labF4N : Nat → Nat × Nat × Nat
  | 1 => (0, 1, 1)
  | 3 => (1, 2, 1)
  | 4 => (15, 0, 1)
  | 6 => (1, 3, 1)
  | 9 => (3, 3, 1)
  | 12 => (4, 4, 1)
  | 16 => (3, 4, 1)
  | 24 => (9, 0, 1)
  | _ => (0, 0, 0)

@[expose] def labE6RelN : Nat → Nat → Nat × Nat × Nat
  | 1, 0 => (0, 1, 2)
  | 3, 0 => (0, 2, 2)
  | 1, 1 => (0, 1, 1)
  | 3, 3 => (1, 2, 1)
  | 6, 6 => (1, 3, 1)
  | 12, 12 => (4, 4, 1)
  | 4, 2 => (0, 3, 1)
  | 9, 3 => (0, 5, 1)
  | 9, 6 => (5, 4, 1)
  | 16, 12 => (4, 5, 1)
  | 24, 12 => (6, 0, 1)
  | _, _ => (0, 0, 0)

@[expose] def labSLN (n o : Nat) : Nat × Nat × Nat :=
  match n with
  | 1 => (0, 1, 1)
  | 3 => (1, 2, 1)
  | 6 => (1, 3, 1)
  | 10 => (1, 4, 1)
  | 15 => (1, 5, 1)
  | 21 => (1, 6, 1)
  | 28 => (1, 7, 1)
  | 36 => if o = 756 then (1, 8, 1) else (10, 0, 1)
  | 12 => (4, 4, 1)
  | 20 => (5, 5, 1)
  | 30 => (4, 6, 1)
  | 42 => (5, 7, 1)
  | 56 => (4, 8, 1)
  | 63 => (7, 0, 1)
  | 120 => (8, 0, 1)
  | _ => (0, 0, 0)

@[expose] def labelN (m : Fin 6) (n o l : Nat) : Nat × Nat × Nat :=
  match m.val with
  | 0 => labF4N n
  | 1 => labE6RelN n l
  | _ => labSLN n o

@[expose] def labelOf (T : Tabs) (m : Fin 6) (c : Nat) : Nat × Nat × Nat :=
  labelN m (cardN (nroots m) c) (orthN T (nroots m) c) (longN (nroots m) c)

@[expose] def lam2N : Nat × Nat × Nat → Bool
  | (t, r, n) => decide (1 ≤ n) &&
    match t with
    | 0 => decide (1 ≤ r) && (r != 1 || decide (2 ≤ n))
    | 1 => decide (2 ≤ r) && (r != 2 || decide (2 ≤ n))
    | 2 | 3 => decide (2 ≤ r) && (r != 2 || decide (2 ≤ n))
    | 4 => decide (3 ≤ r)
    | 5 => decide (2 ≤ r)
    | 6 | 7 | 8 | 9 | 10 | 11 => r == 0
    | 12 => r == 0 && decide (2 ≤ n)
    | 13 | 14 => r == 0 && n % 2 == 1 && decide (3 ≤ n)
    | 15 | 16 | 17 => r == 0 && n == 1
    | _ => false

@[expose] def q2N : Nat × Nat × Nat → Bool
  | (t, r, n) => decide (n < 2) || (t == 0 && r == 1 && n == 2)

@[expose] def twoNodeN : Nat × Nat × Nat → Nat × Nat × Nat → Bool
  | (xt, xr, xn), (jt, jr, jn) =>
    (jt == 0 && xt == 0 && xr == jr + 2 && xn == jn && (jr + 3) % 3 == 0 &&
        (2 ^ jn - 1) % 3 == 0) ||
      (jt == 1 && xt == 1 && xr == jr + 2 && xn == jn && (jr + 3) % 3 == 0 &&
        (2 ^ jn + 1) % 3 == 0) ||
      (jt == 4 && jr == 4 && xt == 6 && xn == jn && (2 ^ jn - 1) % 3 == 0) ||
      (jt == 4 && jr == 4 && xt == 10 && xn == jn && (2 ^ jn + 1) % 3 == 0)

@[expose] def notB2 (m : Fin 6) (c : Nat) : Bool :=
  !(m.val == 0 && cardN (nroots m) c == 4)

@[expose] def derivN (T : Tabs) (r gens : Nat) (L : List (Nat × Nat)) : Option Nat :=
  L.foldl (fun acc e => acc.bind fun S =>
    if decide (e.1 < r) && decide (e.2 < r) && gens.testBit e.1 && S.testBit e.2 then
      some (S ||| 1 <<< T.rt[e.1]![e.2]!)
    else none) (some gens)

@[expose] def genOK (T : Tabs) (r gens c : Nat) (L : List (Nat × Nat)) : Bool :=
  decide (gens < 2 ^ r) && subN gens c &&
    match derivN T r gens L with
    | some S => subN (trunc r c) S
    | none => false

@[expose] def joinOK (T : Tabs) (r ℓ k t : Nat) (L : List (Nat × Nat)) : Bool :=
  decide (t < r) &&
    match derivN T r (trunc r ℓ ||| trunc r k) L with
    | some S => S.testBit t
    | none => false

structure LinW where
  tc : Nat
  n : Nat
  nodes : List Nat
  neg : List Bool
  a : Nat
  b : Nat
  deriving Inhabited

@[expose] def rkN (tc n : Nat) : Nat :=
  match tc with
  | 0 | 1 | 2 | 3 => n
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | _ => 2

@[expose] def validN (tc n : Nat) : Bool :=
  match tc with
  | 0 => decide (1 ≤ n)
  | 1 => decide (2 ≤ n)
  | 2 => decide (3 ≤ n)
  | 3 => decide (4 ≤ n)
  | 4 | 5 | 6 | 7 | 8 => true
  | _ => false

@[expose] def cartanN (tc n i j : Nat) : Int :=
  if i = j then 2 else
  match tc with
  | 0 => if i + 1 = j ∨ j + 1 = i then -1 else 0
  | 1 => if i + 1 = j then (if j = n - 1 then -2 else -1) else if j + 1 = i then -1 else 0
  | 2 => if i + 1 = j then -1 else if j + 1 = i then (if i = n - 1 then -2 else -1) else 0
  | 3 =>
    if n ≤ 2 then 0
    else if i + 1 = j ∧ j + 2 < n then -1
    else if j + 1 = i ∧ i + 2 < n then -1
    else if i + 3 = n ∧ (j + 2 = n ∨ j + 1 = n) then -1
    else if j + 3 = n ∧ (i + 2 = n ∨ i + 1 = n) then -1
    else 0
  | 4 | 5 | 6 =>
    if i = 0 ∧ j = 2 ∨ j = 0 ∧ i = 2 ∨ i = 1 ∧ j = 3 ∨ j = 1 ∧ i = 3 ∨ 2 ≤ i ∧ i + 1 = j ∨
        2 ≤ j ∧ j + 1 = i then -1
    else 0
  | 7 =>
    if i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 ∨ i = 2 ∧ j = 1 ∨ i = 2 ∧ j = 3 ∨ i = 3 ∧ j = 2 then -1
    else if i = 1 ∧ j = 2 then -2
    else 0
  | _ => if i = 0 ∧ j = 1 then -3 else if i = 1 ∧ j = 0 then -1 else 0

@[expose] def sgnN (w : LinW) (i : Nat) : Int := if w.neg.getD i false then -1 else 1

@[expose] def nodeN (w : LinW) (i : Nat) : Nat := w.nodes.getD i 0

@[expose] def nodeMask (w : LinW) (p : Nat → Bool) : Nat :=
  Nat.fold (rkN w.tc w.n) (fun i _ acc => if p i then acc ||| 1 <<< nodeN w i else acc) 0

@[expose] def nodeList (w : LinW) (p : Nat → Bool) : List Nat :=
  ((List.range (rkN w.tc w.n)).filter p).map (nodeN w)

@[expose] def leafN (tc n a : Nat) : Bool :=
  ((List.range (rkN tc n)).filter fun c => c != a && cartanN tc n a c != 0).length == 1

@[expose] def typeOK (T : Tabs) (r : Nat) (w : LinW) : Bool :=
  let k := rkN w.tc w.n
  validN w.tc w.n && w.nodes.length == k && w.nodes.all (fun t => decide (t < r)) &&
    Nat.all k fun i _ => Nat.all k fun j _ =>
      sgnN w i * sgnN w j * T.pair[nodeN w i]![nodeN w j]! == cartanN w.tc w.n i j

@[expose] def linOK (T : Tabs) (r : Nat) (w : LinW) : Bool :=
  typeOK T r w && decide (w.a < rkN w.tc w.n) && decide (w.b < rkN w.tc w.n) && w.a != w.b &&
    leafN w.tc w.n w.a

@[expose] def unsignedN (w : LinW) : Bool := w.neg.all fun s => !s

inductive RefL where
  | zero
  | disc (S : Nat)
  | cent (w : Nat)
  | label
  | q2
  | ins (coef : List (Nat × Nat))
  | outs (φ : Nat)
  deriving Inhabited

inductive RefP where
  | disc (S : Nat)
  | cent (w : Nat)
  | label
  deriving Inhabited

@[expose] def offPlane (d cv cy w : Nat) : Bool :=
  Nat.all 3 fun a _ => Nat.all 3 fun b _ => w != combN d cv cy a b

@[expose] def discOK (T : Tabs) (r c S : Nat) : Bool := trunc r c == 0 || closedOK T r c S

@[expose] def refLOK (T : Tabs) (m : Fin 6) (ext q2 : Bool) (cv : Nat) : RefL → Bool
  | .zero => cv == 0
  | .disc S => discOK T (nroots m) (T.zm[cv]!) S
  | .cent w => decide (w < 3 ^ dim m) && subN (trunc (nroots m) (T.zm[cv]!)) (T.zm[w]!) &&
      offPlane (dim m) cv 0 w
  | .label => !lam2N (labelOf T m (T.zm[cv]!))
  | .q2 => q2 && !q2N (labelOf T m (T.zm[cv]!))
  | .ins coef => ext && inOK T (dim m) (nroots m) (T.zm[cv]!) coef cv
  | .outs φ => !ext && outOK T (dim m) (nroots m) (T.zm[cv]!) φ cv

@[expose] def refPOK (T : Tabs) (m : Fin 6) (cv cy : Nat) : RefP → Bool
  | .disc S => discOK T (nroots m) (T.zm[cv]! &&& T.zm[cy]!) S
  | .cent w => decide (w < 3 ^ dim m) &&
      subN (trunc (nroots m) (T.zm[cv]! &&& T.zm[cy]!)) (T.zm[w]!) && offPlane (dim m) cv cy w
  | .label => !lam2N (labelOf T m (T.zm[cv]! &&& T.zm[cy]!))

inductive RefC where
  | disc (S : Nat)
  | cent (w : Nat)
  | label
  | inCent
  deriving Inhabited

@[expose] def refCOK (T : Tabs) (m : Fin 6) (cv cz : Nat) : RefC → Bool
  | .disc S => discOK T (nroots m) (T.zm[cz]!) S
  | .cent w => decide (w < 3 ^ dim m) && subN (trunc (nroots m) (T.zm[cz]!)) (T.zm[w]!) &&
      offPlane (dim m) cz 0 w
  | .label => !lam2N (labelOf T m (T.zm[cz]!))
  | .inCent => subN (trunc (nroots m) (T.zm[cz]!)) (T.zm[cv]!)

structure Search where
  line : Nat → Option RefL
  plane : Nat → Nat → Option RefP
  cand : Nat → Nat → Option RefC
  deriving Inhabited

@[expose] def scanN (T : Tabs) (m : Fin 6) (ext q2 : Bool) (S : Search)
    (body : Nat → Nat → Bool) : Bool :=
  Nat.all (3 ^ dim m) fun cv _ =>
    (match S.line cv with
      | some e => refLOK T m ext q2 cv e
      | none => false) ||
    Nat.all (3 ^ dim m) fun cy _ =>
      !canonN (dim m) cv cy ||
        (match S.plane cv cy with
          | some e => refPOK T m cv cy e
          | none => false) ||
        body cv cy

@[expose] def scanLineN (T : Tabs) (m : Fin 6) (ext q2 : Bool) (S : Search)
    (body : Nat → Nat → Bool) (cv : Nat) : Bool :=
  (match S.line cv with
    | some e => refLOK T m ext q2 cv e
    | none => false) ||
  Nat.all (3 ^ dim m) fun cy _ =>
    !canonN (dim m) cv cy ||
      (match S.plane cv cy with
        | some e => refPOK T m cv cy e
        | none => false) ||
      body cv cy

@[expose] def scanRangeN (T : Tabs) (m : Fin 6) (ext q2 : Bool) (S : Search)
    (body : Nat → Nat → Bool) (lo n : Nat) : Bool :=
  Nat.all (min n (3 ^ dim m - lo)) fun i _ => scanLineN T m ext q2 S body (lo + i)

@[expose] def candScanN (T : Tabs) (m : Fin 6) (S : Search) (cv cy : Nat)
    (body : Nat → Nat → Bool) : Bool :=
  Nat.all 3 fun a _ => Nat.all 2 fun b' _ =>
    (match S.cand cv (combN (dim m) cv cy a (b' + 1)) with
      | some e => refCOK T m cv (combN (dim m) cv cy a (b' + 1)) e
      | none => false) ||
      body a (b' + 1)

@[expose] def candOK (T : Tabs) (m : Fin 6) (cv cz : Nat) (rows : List Nat)
    (B : Array (Array Int)) : Bool :=
  let k := T.zm[cz]!
  decide (cz < 3 ^ dim m) && connN T (nroots m) k && lineOK T (dim m) (nroots m) rows cz B &&
    lam2N (labelOf T m k) && !subN (trunc (nroots m) k) (T.zm[cv]!) && notB2 m k

structure CommonW where
  w : LinW
  Lℓ : List (Nat × Nat)
  Lk : List (Nat × Nat)
  Bℓ : Array (Array Int)
  Bk : Array (Array Int)
  deriving Inhabited

@[expose] def commonOK (T : Tabs) (m : Fin 6) (cv cz ℓ k : Nat) (W : CommonW) : Bool :=
  let r := nroots m
  linOK T r W.w &&
    genOK T r (nodeMask W.w fun i => i != W.w.a) ℓ W.Lℓ &&
    genOK T r (nodeMask W.w fun i => i != W.w.b) k W.Lk &&
    lineOK T (dim m) r (nodeList W.w fun i => i != W.w.a) cv W.Bℓ &&
    lineOK T (dim m) r (nodeList W.w fun i => i != W.w.b) cz W.Bk &&
    notB2 m ℓ && notB2 m k

@[expose] def leafModelOK (T : Tabs) (m : Fin 6) (cv cz ℓ k : Nat) (W : CommonW) : Bool :=
  commonOK T m cv cz ℓ k W && leafN W.w.tc W.w.n W.w.b

@[expose] def nbrOK (T : Tabs) (m : Fin 6) (cz k : Nat) (w : LinW) (L : List (Nat × Nat))
    (B : Array (Array Int)) : Bool :=
  let r := nroots m
  linOK T r w && genOK T r (nodeMask w fun _ => true) k L &&
    lineOK T (dim m) r (nodeList w fun _ => true) cz B && notB2 m k

@[expose] def selE6OK (T : Tabs) (m : Fin 6) (k : Nat) (w : LinW) (L : List (Nat × Nat)) : Bool :=
  w.tc == 4 && unsignedN w && typeOK T (nroots m) w &&
    genOK T (nroots m) (nodeMask w fun _ => true) k L && notB2 m k

@[expose] def selD6OK (T : Tabs) (m : Fin 6) (j k : Nat) (w : LinW) (L L' : List (Nat × Nat)) :
    Bool :=
  w.tc == 3 && w.n == 6 && (w.b == 4 || w.b == 5) && typeOK T (nroots m) w &&
    genOK T (nroots m) (nodeMask w fun _ => true) k L &&
    genOK T (nroots m) (nodeMask w fun i => i != w.b) j L' && notB2 m j && notB2 m k

@[expose] def indepOK (T : Tabs) (d : Nat) (w : LinW) (B : Array (Array Int)) : Bool :=
  let k := rkN w.tc w.n
  Nat.all k fun i _ => Nat.all k fun j _ =>
    (Nat.fold d (fun l _ s => s + T.h[nodeN w i]![l]! * B[l]![j]!) 0 -
      (if i = j then 1 else 0)) % 3 == 0

@[expose] def basisOK (T : Tabs) (d : Nat) (w : LinW) (B : Array (Array Int)) : Bool :=
  rkN w.tc w.n == d && indepOK T d w B

@[expose] def invOK (k : Nat) (M : Nat → Nat → Int) (B : Array (Array Int)) : Bool :=
  Nat.all k fun i _ => Nat.all k fun j _ =>
    (Nat.fold k (fun l _ s => s + B[i]![l]! * M l j) 0 - (if i = j then 1 else 0)) % 3 == 0

@[expose] def singOK (k : Nat) (M : Nat → Nat → Int) (x : Array Int) : Bool :=
  (List.range k).any (fun l => x[l]! % 3 != 0) &&
    Nat.all k fun i _ => (Nat.fold k (fun l _ s => s + M i l * x[l]!) 0) % 3 == 0

@[expose] def offN (a p : Nat) : Nat := if p < a then p else p + 1

@[expose] def detOK (w : LinW) (B B' : Array (Array Int)) : Bool :=
  invOK (rkN w.tc w.n) (cartanN w.tc w.n) B &&
    invOK (rkN w.tc w.n - 1) (fun p q => cartanN w.tc w.n (offN w.a p) (offN w.a q)) B'

structure AmbW where
  w : LinW
  Lk : List (Nat × Nat)
  La : List (Nat × Nat)
  Bk : Array (Array Int)
  Bb : Array (Array Int)
  deriving Inhabited

@[expose] def ambOK (T : Tabs) (m : Fin 6) (cv cz ℓ k : Nat) (W : AmbW) : Bool :=
  let r := nroots m
  linOK T r W.w &&
    genOK T r (nodeMask W.w fun i => i != W.w.a) k W.Lk &&
    lineOK T (dim m) r (nodeList W.w fun i => i != W.w.a) cz W.Bk &&
    joinOK T r ℓ k (nodeN W.w W.w.a) W.La &&
    decide (cv < 3 ^ dim m) &&
    (nodeList W.w fun i => i != W.w.a && i != W.w.b).all (fun t => (T.zm[cv]!).testBit t) &&
    basisOK T (dim m) W.w W.Bb && notB2 m ℓ && notB2 m k

@[expose] def ambientOK (T : Tabs) (m : Fin 6) (cv cz ℓ k : Nat) (W : AmbW)
    (B B' : Array (Array Int)) : Bool :=
  ambOK T m cz cv k ℓ W && detOK W.w B B'

@[expose] def ambDOK (T : Tabs) (m : Fin 6) (cv cz ℓ k : Nat) (W : AmbW) (perm : List Nat)
    (h : Nat) : Bool :=
  ambOK T m cv cz ℓ k W && decide (3 ≤ h) && rkN W.w.tc W.w.n == 2 * h + 1 &&
    perm.length == 2 * h && decide perm.Nodup &&
    perm.all (fun i => decide (i < rkN W.w.tc W.w.n) && i != W.w.a) &&
    Nat.all (2 * h) fun i _ => Nat.all (2 * h) fun j _ =>
      cartanN W.w.tc W.w.n (perm.getD i 0) (perm.getD j 0) == cartanN 3 (2 * h) i j

@[expose] def d5OK (T : Tabs) (m : Fin 6) (cv cz ℓ j k : Nat) (W : AmbW)
    (Lj : List (Nat × Nat)) : Bool :=
  ambOK T m cv cz ℓ k W && W.w.tc == 3 && W.w.n == 5 && W.w.a == 0 &&
    (W.w.b == 1 || W.w.b == 3 || W.w.b == 4) &&
    genOK T (nroots m) (nodeMask W.w fun i => i != W.w.a && i != W.w.b) j Lj && notB2 m j &&
    (labelOf T m j == (1, 3, 1) || labelOf T m j == (5, 3, 1))

end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
