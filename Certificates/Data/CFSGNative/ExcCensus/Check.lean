module

public import Certificates.Data.CFSGNative.ExcCensus.Core
public import Std.Data.HashMap

public section

open Std

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

set_option compiler.extract_closed false

structure CSearch where
  S : Search
  twoNode : Nat → Nat → Option (Nat × Nat × List Nat × Array (Array Int) × Nat)
  common : Nat → Nat → Option (Nat × Nat × List Nat × Array (Array Int) × CommonW)
  amb : Nat → Nat → Option (AmbW × Array (Array Int) × Array (Array Int))
  deriving Inhabited

@[expose] def bodyCC (T : Tabs) (m : Fin 6) (X : CSearch) (cv cy : Nat) : Bool :=
  let d := dim m
  let ℓ := T.zm[cv]!
  let j := T.zm[cv]! &&& T.zm[cy]!
  twoNodeN (labelOf T m ℓ) (labelOf T m j) ||
    (match X.twoNode cv cy with
      | some (a, b, rows, B, φ) =>
        decide (a < 3) && (b == 1 || b == 2) && candOK T m cv (combN d cv cy a b) rows B &&
          outOK T d (nroots m) (T.zm[combN d cv cy a b]!) φ (combN d cv cy a b) &&
          twoNodeN (labelOf T m (T.zm[combN d cv cy a b]!)) (labelOf T m j)
      | none => false) ||
    (match X.common cv cy with
      | some (a, b, rows, B, W) =>
        decide (a < 3) && (b == 1 || b == 2) && candOK T m cv (combN d cv cy a b) rows B &&
          commonOK T m cv (combN d cv cy a b) ℓ (T.zm[combN d cv cy a b]!) W
      | none => false) ||
    candScanN T m X.S cv cy fun a b =>
      twoNodeN (labelOf T m (T.zm[combN d cv cy a b]!)) (labelOf T m j) ||
        match X.amb cv (combN d cv cy a b) with
        | some (W, B, B') => ambientOK T m cv (combN d cv cy a b) ℓ (T.zm[combN d cv cy a b]!) W B B'
        | none => false

@[expose] def censusOK (m : Fin 6) (T : Tabs) (X : CSearch) : Bool :=
  tabsOK m T && scanN T m true false X.S (bodyCC T m X)

structure LSearch where
  S : Search
  leaf : Nat → Nat → Option CommonW
  d6 : Nat → Nat → Option (LinW × List (Nat × Nat) × List (Nat × Nat))
  e6 : Nat → Option (LinW × List (Nat × Nat))
  deriving Inhabited

@[expose] def bodyIL (T : Tabs) (m : Fin 6) (X : LSearch) (cv cy : Nat) : Bool :=
  let d := dim m
  let j := T.zm[cv]! &&& T.zm[cy]!
  candScanN T m X.S cv cy fun a b =>
    (match X.leaf cv (combN d cv cy a b) with
      | some W => leafModelOK T m cv (combN d cv cy a b) (T.zm[cv]!) (T.zm[combN d cv cy a b]!) W
      | none => false) ||
    (match X.d6 j (T.zm[combN d cv cy a b]!) with
      | some (w, L, L') => selD6OK T m j (T.zm[combN d cv cy a b]!) w L L'
      | none => false) ||
    (match X.e6 (T.zm[combN d cv cy a b]!) with
      | some (w, L) => selE6OK T m (T.zm[combN d cv cy a b]!) w L
      | none => false)

@[expose] def inLSelOK (m : Fin 6) (T : Tabs) (X : LSearch) : Bool :=
  tabsOK m T && scanN T m false true X.S (bodyIL T m X)

def rtSearch (T : Tabs) (d r u t : Nat) : Nat :=
  ((List.range r).find? fun t' => rtEq T d t' u t 1 || rtEq T d t' u t (-1)).getD 0

def tabsOf (m : Fin 6) : Tabs :=
  let d := dim m
  let r := nroots m
  let f := (Array.range r).map fun i => (Array.range d).map fun k => fN m i k
  let h := (Array.range r).map fun i => (Array.range d).map fun k => hN m i k
  let pair := (Array.range r).map fun i => (Array.range r).map fun j => pairN m i j
  let T0 : Tabs := { f, h, pair, adj := #[], zm := #[], rt := #[] }
  let adj := (Array.range r).map fun i => adjA T0 r i
  let zm := (Array.range (3 ^ d)).map fun c => zmA T0 d r c
  let T1 : Tabs := { T0 with adj, zm }
  { T1 with rt := (Array.range r).map fun u => (Array.range r).map fun t => rtSearch T1 d r u t }

def m3 (x : Int) : Nat := (x % 3).toNat

def digsS (d c : Nat) : Array Nat := (Array.range d).map fun k => dig c k

def codeS (v : Array Nat) : Nat :=
  (v.foldl (fun (acc : Nat × Nat) x => (acc.1 + x % 3 * acc.2, acc.2 * 3)) (0, 1)).1

def rref3 (rows : Array (Array Nat)) (nc : Nat) : Array (Array Nat) × Array Nat := Id.run do
  let mut R : Array (Array Nat) := rows.map (·.map (· % 3))
  let m := R.size
  let mut piv : Array Nat := #[]
  let mut k := 0
  for j in [0:nc] do
    if k < m then
      let mut q : Option Nat := none
      for i in [k:m] do
        if q.isNone && R[i]![j]! != 0 then q := some i
      match q with
      | none => pure ()
      | some qq =>
        let rk := R[k]!
        R := (R.set! k R[qq]!).set! qq rk
        let t := R[k]![j]!
        R := R.set! k (R[k]!.map fun x => (x * t) % 3)
        let rowk := R[k]!
        for i in [0:m] do
          if i != k && R[i]![j]! != 0 then
            let t := R[i]![j]!
            let rowi := R[i]!
            R := R.set! i ((Array.range nc).map fun c => (rowi[c]! + 3 - (t * rowk[c]!) % 3) % 3)
        piv := piv.push j
        k := k + 1
  return (R.extract 0 k, piv)

def null3 (rows : Array (Array Nat)) (d : Nat) : Array (Array Nat) := Id.run do
  let (R, piv) := rref3 rows d
  let mut out : Array (Array Nat) := #[]
  for j in [0:d] do
    if !piv.contains j then
      let mut v : Array Nat := Array.replicate d 0
      v := v.set! j 1
      for i in [0:piv.size] do
        v := v.set! piv[i]! ((3 - R[i]![j]!) % 3)
      out := out.push v
  return out

def inv3 (M : Array (Array Int)) (n : Nat) : Option (Array (Array Int)) :=
  let aug := (Array.range n).map fun i =>
    ((Array.range n).map fun j => m3 M[i]![j]!) ++ (Array.range n).map fun j => if i == j then 1 else 0
  let (R, piv) := rref3 aug (2 * n)
  if piv.size == n && (List.range n).all (fun i => piv[i]! == i) then
    some (R.map fun row => (row.extract n (2 * n)).map fun (x : Nat) => (x : Int))
  else none

def solve3 (idx : Array Nat) (vecs : Array (Array Nat)) (v : Array Nat) (d : Nat) :
    Option (List (Nat × Nat)) :=
  let n := vecs.size
  let aug := (Array.range d).map fun k => ((Array.range n).map fun t => vecs[t]![k]! % 3).push v[k]!
  let (R, piv) := rref3 aug (n + 1)
  if piv.contains n then none
  else some ((List.range piv.size).filterMap fun i =>
    let x := R[i]![n]!
    if x == 0 then none else some (idx[piv[i]!]!, x))

def bitsS (r c : Nat) : Array Nat := (Array.range r).filter fun t => c.testBit t

def maskS (l : List Nat) : Nat := l.foldl (fun acc i => acc ||| 1 <<< i) 0

def compS (T : Tabs) (r c : Nat) : Nat := Id.run do
  let c' := trunc r c
  if c' == 0 then return 0
  let mut comp := 1 <<< lowN r c'
  let mut front := comp
  while front != 0 do
    let mut nb := 0
    for t in [0:r] do
      if front.testBit t then nb := nb ||| T.adj[t]!
    nb := nb &&& c'
    nb := nb ^^^ (nb &&& comp)
    comp := comp ||| nb
    front := nb
  return comp

def discS (T : Tabs) (r c : Nat) : Option Nat :=
  let c' := trunc r c
  if c' == 0 then some 0 else
    let C := compS T r c
    if C != c' then some C else none

def fRows (T : Tabs) (r c : Nat) : Array (Array Nat) := (bitsS r c).map fun t => (T.f[t]!).map m3

def hRows (T : Tabs) (r c : Nat) : Array (Array Nat) := (bitsS r c).map fun t => (T.h[t]!).map m3

def centS (T : Tabs) (d r c cv cy : Nat) : Option Nat :=
  ((null3 (fRows T r c) d).map codeS).find? fun w => offPlane d cv cy w

def insS (T : Tabs) (d r c cv : Nat) : Option (List (Nat × Nat)) :=
  solve3 (bitsS r c) (hRows T r c) (digsS d cv) d

def outsS (T : Tabs) (d r c cv : Nat) : Option Nat :=
  ((null3 (hRows T r c) d).map codeS).find? fun φ =>
    Nat.fold d (fun k _ s => s + (dig φ k : Int) * (dig cv k : Int)) 0 % 3 != 0

def lineS (T : Tabs) (m : Fin 6) (ext q2 : Bool) (cv : Nat) : Option RefL :=
  let d := dim m
  let r := nroots m
  let ℓ := T.zm[cv]!
  if cv == 0 then some .zero else
  match discS T r ℓ with
  | some S => some (.disc S)
  | none =>
    match centS T d r ℓ cv 0 with
    | some w => some (.cent w)
    | none =>
      if !lam2N (labelOf T m ℓ) then some .label
      else if q2 && !q2N (labelOf T m ℓ) then some .q2
      else if ext then (insS T d r ℓ cv).map .ins
      else (outsS T d r ℓ cv).map .outs

def planeS (T : Tabs) (m : Fin 6) (cv cy : Nat) : Option RefP :=
  let d := dim m
  let r := nroots m
  let j := T.zm[cv]! &&& T.zm[cy]!
  match discS T r j with
  | some S => some (.disc S)
  | none =>
    match centS T d r j cv cy with
    | some w => some (.cent w)
    | none => if !lam2N (labelOf T m j) then some .label else none

def candS (T : Tabs) (m : Fin 6) (cv cz : Nat) : Option RefC :=
  let d := dim m
  let r := nroots m
  let k := T.zm[cz]!
  if subN (trunc r k) (T.zm[cv]!) then some .inCent else
  match discS T r k with
  | some S => some (.disc S)
  | none =>
    match centS T d r k cz 0 with
    | some w => some (.cent w)
    | none => if !lam2N (labelOf T m k) then some .label else none

def searchS (T : Tabs) (m : Fin 6) (ext q2 : Bool) : Search where
  line := lineS T m ext q2
  plane := planeS T m
  cand := candS T m

def rootIdx (m : Fin 6) : HashMap (Array Int) Nat :=
  let m' : Fin 6 := if m.val = 3 then 2 else m
  let d := dim m'
  (List.range (nroots m)).foldl
    (fun acc i => acc.insert ((Array.range d).map fun k => fN m' i k) i) {}

def simpleS (m : Fin 6) (ix : HashMap (Array Int) Nat) (r c : Nat) : List Nat :=
  let m' : Fin 6 := if m.val = 3 then 2 else m
  let d := dim m'
  let vec (i : Nat) : Array Int := (Array.range d).map fun k => fN m' i k
  let ids := (bitsS r c).toList
  ids.filter fun i =>
    !(ids.any fun j => j != i &&
      match ix[(Array.range d).map fun k => (vec i)[k]! - (vec j)[k]!]? with
      | some t => c.testBit t
      | none => false)

def closureS (T : Tabs) (r : Nat) (gens : List Nat) : Nat × List (Nat × Nat) := Id.run do
  let mut S := maskS gens
  let mut steps : Array (Nat × Nat) := #[]
  let mut todo : Array Nat := gens.toArray
  while todo.size > 0 do
    let t := todo.back!
    todo := todo.pop
    for u in gens do
      if u < r && t < r then
        let t' := T.rt[u]![t]!
        if !S.testBit t' then
          S := S ||| 1 <<< t'
          steps := steps.push (u, t)
          todo := todo.push t'
  return (S, steps.toList)

def extsS (T : Tabs) (r : Nat) (ss : List Nat) (common X : Nat) : List (Nat × Bool) :=
  (bitsS r (X ^^^ (X &&& common))).toList.foldr (fun i acc =>
    let ok (sg : Int) := ss.all fun j => sg * T.pair[i]![j]! ≤ 0 && sg * T.pair[j]![i]! ≤ 0
    let p := ok 1
    let n := ok (-1)
    if (p || n) && subN (trunc r X) (closureS T r (i :: ss)).1 then
      (if p then [(i, false)] else []) ++ (if n then [(i, true)] else []) ++ acc
    else acc) []

def cartanS (T : Tabs) (V : Array (Nat × Bool)) : Array (Array Int) :=
  V.map fun x => V.map fun y =>
    (if x.2 then -1 else 1) * (if y.2 then -1 else 1) * T.pair[x.1]![y.1]!

def assignS (C : Array (Array Int)) (tc n : Nat) : Nat → Array Nat → Option (Array Nat)
  | 0, π => if π.size == C.size then some π else none
  | fuel + 1, π =>
    let i := π.size
    if i == C.size then some π else
      (List.range C.size).findSome? fun x =>
        if π.contains x || C[x]![x]! != 2 then none
        else if (List.range i).all fun j =>
            C[x]![π[j]!]! == cartanN tc n i j && C[π[j]!]![x]! == cartanN tc n j i then
          assignS C tc n fuel (π.push x)
        else none

def identifyS (C : Array (Array Int)) : Option (Nat × Nat × Array Nat) :=
  let r := C.size
  let types : List (Nat × Nat) := [(0, r), (1, r), (2, r), (3, r), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0)]
  types.findSome? fun (tc, n) =>
    if validN tc n && rkN tc n == r then (assignS C tc n r #[]).map fun π => (tc, n, π)
    else none

def posS (π : Array Nat) (x : Nat) : Nat := ((List.range π.size).find? fun i => π[i]! == x).getD 0

def linS (V : Array (Nat × Bool)) (tc n : Nat) (π : Array Nat) (ia ib : Nat) : LinW where
  tc := tc
  n := n
  nodes := (π.map fun x => V[x]!.1).toList
  neg := (π.map fun x => V[x]!.2).toList
  a := posS π ia
  b := posS π ib

def lineB (T : Tabs) (d : Nat) (rows : List Nat) (cz : Nat) : Array (Array Int) :=
  let p := pivN d cz
  let Φ := (Array.range d).map fun i => (Array.range d).map fun j => phiN T d p rows i j
  (inv3 Φ d).getD #[]

def lineS' (T : Tabs) (d r k cz : Nat) : List Nat × Array (Array Int) := Id.run do
  let mut rows : Array Nat := #[]
  let mut F : Array (Array Nat) := #[]
  for t in bitsS r k do
    if rows.size + 1 < d then
      let F' := F.push ((T.f[t]!).map m3)
      if (rref3 F' d).2.size == F'.size then
        rows := rows.push t
        F := F'
  return (rows.toList, lineB T d rows.toList cz)

def modelS (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (leaf : Bool) (cv cz : Nat) :
    Option CommonW :=
  let d := dim m
  let r := nroots m
  let ℓ := T.zm[cv]!
  let k := T.zm[cz]!
  let common := ℓ &&& k
  let ss := simpleS m ix r common
  if ss.length + 2 != d then none else
  let eL := extsS T r ss common ℓ
  let eK := extsS T r ss common k
  eL.findSome? fun b' => eK.findSome? fun a' =>
    let V : Array (Nat × Bool) := (ss.map fun i => (i, false)).toArray ++ #[b', a']
    match identifyS (cartanS T V) with
    | none => none
    | some (tc, n, π) =>
      let w := linS V tc n π (V.size - 1) (V.size - 2)
      let offA := nodeList w fun i => i != w.a
      let offB := nodeList w fun i => i != w.b
      let W : CommonW :=
        { w, Lℓ := (closureS T r offA).2, Lk := (closureS T r offB).2,
          Bℓ := lineB T d offA cv, Bk := lineB T d offB cz }
      if (if leaf then leafModelOK T m cv cz ℓ k W else commonOK T m cv cz ℓ k W) then some W
      else none

def ambS (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (j cv cz : Nat) :
    Option (AmbW × Array (Array Int) × Array (Array Int)) :=
  let d := dim m
  let r := nroots m
  let ℓ := T.zm[cv]!
  let k := T.zm[cz]!
  let (psi, Lpsi) := closureS T r (bitsS r (trunc r ℓ ||| trunc r k)).toList
  let ss := simpleS m ix r j
  if ss.length + 2 != d then none else
  (extsS T r ss j ℓ).findSome? fun b' =>
    (bitsS r (psi ^^^ (psi &&& ℓ))).toList.findSome? fun i =>
      [false, true].findSome? fun sg =>
        let V : Array (Nat × Bool) := (ss.map fun i => (i, false)).toArray ++ #[b', (i, sg)]
        match identifyS (cartanS T V) with
        | none => none
        | some (tc, n, π) =>
          let w := linS V tc n π (V.size - 1) (V.size - 2)
          let rk := rkN tc n
          let offA := nodeList w fun i => i != w.a
          let Hm := (Array.range rk).map fun i => T.h[nodeN w i]!
          let Cm := (Array.range rk).map fun i => (Array.range rk).map fun j => cartanN tc n i j
          let Cm' := (Array.range (rk - 1)).map fun p => (Array.range (rk - 1)).map fun q =>
            cartanN tc n (offN w.a p) (offN w.a q)
          let W : AmbW :=
            { w, Lk := (closureS T r offA).2, La := Lpsi, Bk := lineB T d offA cv,
              Bb := (inv3 Hm rk).getD #[] }
          let B := (inv3 Cm rk).getD #[]
          let B' := (inv3 Cm' (rk - 1)).getD #[]
          if ambientOK T m cv cz ℓ k W B B' then some (W, B, B') else none

def twoNodeS (T : Tabs) (m : Fin 6) (cv cy : Nat) :
    Option (Nat × Nat × List Nat × Array (Array Int) × Nat) :=
  let d := dim m
  let r := nroots m
  let j := T.zm[cv]! &&& T.zm[cy]!
  [(0, 1), (1, 1), (2, 1), (0, 2), (1, 2), (2, 2)].findSome? fun (a, b) =>
    let cz := combN d cv cy a b
    let k := T.zm[cz]!
    if !twoNodeN (labelOf T m k) (labelOf T m j) then none else
    match outsS T d r k cz with
    | none => none
    | some φ =>
      let (rows, B) := lineS' T d r k cz
      if candOK T m cv cz rows B then some (a, b, rows, B, φ) else none

def commonS (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (cv cy : Nat) :
    Option (Nat × Nat × List Nat × Array (Array Int) × CommonW) :=
  let d := dim m
  let r := nroots m
  [(0, 1), (1, 1), (2, 1), (0, 2), (1, 2), (2, 2)].findSome? fun (a, b) =>
    let cz := combN d cv cy a b
    let (rows, B) := lineS' T d r (T.zm[cz]!) cz
    if !candOK T m cv cz rows B then none else
    (modelS T m ix false cv cz).map fun W => (a, b, rows, B, W)

def e6S (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (k : Nat) :
    Option (LinW × List (Nat × Nat)) :=
  let r := nroots m
  let ss := simpleS m ix r k
  let V : Array (Nat × Bool) := (ss.map fun i => (i, false)).toArray
  match identifyS (cartanS T V) with
  | some (4, n, π) =>
    let w := linS V 4 n π 0 1
    let L := (closureS T r w.nodes).2
    if selE6OK T m k w L then some (w, L) else none
  | _ => none

def d6S (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (j k : Nat) :
    Option (LinW × List (Nat × Nat) × List (Nat × Nat)) :=
  let r := nroots m
  let ss := simpleS m ix r j
  (extsS T r ss j k).findSome? fun (i, ng) =>
    let V : Array (Nat × Bool) := ((ss.map fun t => (t, false)).toArray).push (i, ng)
    match identifyS (cartanS T V) with
    | some (3, 6, π) =>
      let b := posS π (V.size - 1)
      let w : LinW := { linS V 3 6 π 0 0 with b }
      let L := (closureS T r w.nodes).2
      let L' := (closureS T r (nodeList w fun t => t != b)).2
      if selD6OK T m j k w L L' then some (w, L, L') else none
    | _ => none

def cSearchOf (m : Fin 6) (T : Tabs) : CSearch :=
  let ix := rootIdx m
  { S := searchS T m true false
    twoNode := twoNodeS T m
    common := commonS T m ix
    amb := fun cv cz =>
      ambS T m ix (T.zm[cv]! &&& T.zm[cz]!) cv cz }

def lSearchOf (m : Fin 6) (T : Tabs) : LSearch :=
  let ix := rootIdx m
  { S := searchS T m false true
    leaf := modelS T m ix true
    d6 := d6S T m ix
    e6 := e6S T m ix }

@[expose] def censusCheck (m : Fin 6) : Bool :=
  let T := tabsOf m
  censusOK m T (cSearchOf m T)

@[expose] def censusRangeCheck (m : Fin 6) (lo n : Nat) : Bool :=
  let T := tabsOf m
  let X := cSearchOf m T
  tabsOK m T && scanRangeN T m true false X.S (bodyCC T m X) lo n

@[expose] def inLSelCheck (m : Fin 6) : Bool :=
  let T := tabsOf m
  inLSelOK m T (lSearchOf m T)

end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
