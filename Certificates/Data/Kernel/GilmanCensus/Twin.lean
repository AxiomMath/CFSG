module

public import Init

public section

namespace Certificates.GilmanCensusK

structure DK where
  mode : Nat
  n : Nat
  d : Nat
  N : Nat
  AR : List (List Nat)
  rho : List Nat
  R : List (List Nat)
  absidx : List (List Nat)
  F : List (List Nat)
  H : List (List Nat)
  G : List (List Nat)
  adj : List Nat
  aadj : List Nat
  reflP : List Nat
  lines : List (List Nat)
  zp : List (Nat × Nat)

@[expose] def DK.full (dk : DK) : Nat := (1 <<< dk.N) - 1

@[expose] def bitsA : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, i, m =>
    if m == 0 then [] else if m % 2 == 1 then i :: bitsA f (i + 1) (m / 2) else bitsA f (i + 1) (m / 2)

@[expose] def bitsK (m : Nat) : List Nat := bitsA 128 0 m

@[expose] def bitK (i : Nat) : Nat := 1 <<< i

@[expose] def hasBitK (m i : Nat) : Bool := (m >>> i) % 2 == 1

@[expose] def popcK (m : Nat) : Nat := (bitsK m).length

@[expose] def dotS : List Nat → List Nat → Nat
  | a :: as, b :: bs => a * b + dotS as bs
  | _, _ => 0

@[expose] def dot3K (v w : List Nat) : Nat := dotS v w % 3

@[expose] def findIn {α : Type} (P : α → Bool) (r0 : α) : List α → Option (α × List α)
  | [] => none
  | r :: tl => if P r then some (r, r0 :: tl) else (findIn P r0 tl).map fun p => (p.1, r :: p.2)

@[expose] def pickQ {α : Type} (P : α → Bool) : List α → Option (α × List α)
  | [] => none
  | r0 :: tl => if P r0 then some (r0, tl) else findIn P r0 tl

@[expose] def subRow (t : Nat) (ri rk : List Nat) : List Nat :=
  List.zipWith (fun a b => (a + 3 - (t * b) % 3) % 3) ri rk

@[expose] def rr3Step (j : Nat) (st : List (List Nat) × List (List Nat) × List Nat) :
    List (List Nat) × List (List Nat) × List Nat :=
  match pickQ (fun r => r.getD j 0 != 0) st.2.1 with
  | none => st
  | some (p, rest) =>
    let t := p.getD j 0
    let pk := p.map fun x => (x * t) % 3
    let el := fun (r : List Nat) => if r.getD j 0 != 0 then subRow (r.getD j 0) r pk else r
    (st.1.map el ++ [pk], rest.map el, st.2.2 ++ [j])

@[expose] def rowRed3K (rows : List (List Nat)) (nc : Nat) : List (List Nat) × List Nat :=
  let st := (List.range nc).foldl (fun st j => rr3Step j st) ([], rows.map (·.map (· % 3)), [])
  (st.1, st.2.2)

@[expose] def rank3K (rows : List (List Nat)) (nc : Nat) : Nat := (rowRed3K rows nc).2.length

@[expose] def nullEnt (R : List (List Nat)) (piv : List Nat) (j c : Nat) : Nat :=
  match (List.zip piv R).find? (·.1 == c) with
  | some p => (3 - p.2.getD j 0) % 3
  | none => if c == j then 1 else 0

@[expose] def null3K (rows : List (List Nat)) (d : Nat) : List (List Nat) :=
  let rp := rowRed3K rows d
  (List.range d).filterMap fun j =>
    if rp.2.contains j then none else some ((List.range d).map (nullEnt rp.1 rp.2 j))

@[expose] def firstNZK : List Nat → Nat
  | [] => 0
  | x :: xs => if x % 3 != 0 then x % 3 else firstNZK xs

@[expose] def line3K (v : List Nat) : List Nat := let t := firstNZK v; v.map fun x => (x * t) % 3

@[expose] def gcdL (r : List Int) : Nat := r.foldl (fun g x => Nat.gcd g x.natAbs) 0

@[expose] def rqStep (j : Nat) (st : List (List Int) × Nat) : List (List Int) × Nat :=
  match pickQ (fun r => r.getD j 0 != 0) st.1 with
  | none => st
  | some (rr, rest) =>
    let p := rr.getD j 0
    (rest.map fun ri =>
      let c := ri.getD j 0
      if c != 0 then
        let nr := List.zipWith (fun a b => p * a - c * b) ri rr
        let g := gcdL nr
        if g > 1 then nr.map (· / (g : Int)) else nr
      else ri, st.2 + 1)

@[expose] def rankQK (rows : List (List Int)) : Nat :=
  match rows with
  | [] => 0
  | r :: _ => ((List.range r.length).foldl (fun st j => rqStep j st) (rows, 0)).2

@[expose] def detStep (n k : Nat) (st : Option (List (List Int) × Int × Int)) :
    Option (List (List Int) × Int × Int) :=
  match st with
  | none => none
  | some (rows, sign, prev) =>
    let sw : Option (List Int × List (List Int) × Int) :=
      match rows with
      | [] => none
      | r0 :: tl =>
        if r0.getD k 0 == 0 then
          (findIn (fun r => r.getD k 0 != 0) r0 tl).map fun p => (p.1, p.2, -sign)
        else some (r0, tl, sign)
    match sw with
    | none => none
    | some (rowk, tl, sign') =>
      some (tl.map (fun rowi => (List.range n).map fun j =>
          if j > k then (rowi.getD j 0 * rowk.getD k 0 - rowi.getD k 0 * rowk.getD j 0) / prev
          else rowi.getD j 0),
        sign', rowk.getD k 0)

@[expose] def detIntK (M : List (List Int)) : Int :=
  let n := M.length
  if n == 0 then 1 else
  match (List.range (n - 1)).foldl (fun st k => detStep n k st) (some (M, 1, 1)) with
  | none => 0
  | some (rows, sign, _) => sign * (rows.getD 0 []).getD (n - 1) 0

@[expose] def typeNameK (n k : Nat) : Nat × Nat :=
  if k == n * (n + 1) / 2 then (0, n)
  else if k == n * (n - 1) && n ≥ 4 then (1, n)
  else if (n == 6 && k == 36) || (n == 7 && k == 63) || (n == 8 && k == 120) then (2, n)
  else if n == 4 && k == 24 then (3, 4)
  else if k == n * n then (4, n)
  else (9, n)

@[expose] def gI (dk : DK) (i j : Nat) : Int := ((dk.G.getD i []).getD j 0 : Int) - 64

@[expose] def fK (dk : DK) (i : Nat) : List Nat := dk.F.getD i []

@[expose] def hK (dk : DK) (i : Nat) : List Nat := dk.H.getD i []

@[expose] def leAll : List Nat → List Nat → Bool
  | b :: bs, a :: as => b ≤ a && leAll bs as
  | _, _ => true

@[expose] def idxOfL (v : List Nat) : List (List Nat) → Nat → Option Nat
  | [], _ => none
  | r :: rs, k => if r == v then some k else idxOfL v rs (k + 1)

@[expose] def subIdx (R : List (List Nat)) (a b : List Nat) : Option Nat :=
  if leAll b a then idxOfL (List.zipWith (· - ·) a b) R 0 else none

@[expose] def rootsOfMaskK (R : List (List Nat)) (m : Nat) : List (List Nat) :=
  (bitsK m).map (R.getD · [])

@[expose] def toI (rs : List (List Nat)) : List (List Int) := rs.map (·.map Int.ofNat)

@[expose] def addS (full : Nat) (a b : Nat × Nat) : Nat × Nat :=
  let za := full ^^^ (a.1 ||| a.2)
  let zb := full ^^^ (b.1 ||| b.2)
  ((a.1 &&& zb) ||| (b.1 &&& za) ||| (a.2 &&& b.2), (a.2 &&& zb) ||| (b.2 &&& za) ||| (a.1 &&& b.1))

@[expose] def smulS (s : Nat) (a : Nat × Nat) : Nat × Nat :=
  if s % 3 == 0 then (0, 0) else if s % 3 == 1 then a else (a.2, a.1)

@[expose] def zerosK (dk : DK) (v : List Nat) : Nat :=
  let s := (List.zip v dk.zp).foldl (fun acc p => addS dk.full acc (smulS p.1 p.2)) (0, 0)
  dk.full ^^^ (s.1 ||| s.2)

@[expose] def nbA : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | a :: as, f, acc => if f == 0 then acc else nbA as (f >>> 1) (if f % 2 == 1 then acc ||| a else acc)

@[expose] def growA (adj : List Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, left, c, _ => (left, c)
  | f + 1, left, c, front =>
    if front == 0 then (left, c) else
    let nb := nbA adj front 0 &&& left
    growA adj f (left ^^^ nb) (c ||| nb) nb

@[expose] def compsA (adj : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, left =>
    if left == 0 then [] else
    let c0 := left ^^^ (left &&& (left - 1))
    let lc := growA adj 128 (left ^^^ c0) c0 c0
    lc.2 :: compsA adj f lc.1

@[expose] def compsK (adj : List Nat) (mask : Nat) : List Nat := compsA adj 128 mask

@[expose] def simpOfK (dk : DK) (mask : Nat) : List Nat :=
  let ids := bitsK mask
  ids.filter fun i =>
    !(ids.any fun j => j != i && match subIdx dk.R (dk.R.getD i []) (dk.R.getD j []) with
        | some k => hasBitK mask k
        | none => false)

@[expose] def kindOfK (dk : DK) (mask : Nat) : Nat × Nat :=
  typeNameK (rankQK (toI (rootsOfMaskK dk.R mask))) (popcK mask)

@[expose] def permVecK (rho r : List Nat) : List Nat :=
  (List.range r.length).map fun j => r.getD (rho.getD j 0) 0

@[expose] def labelPureK (dk : DK) (mask : Nat) : Nat × Bool × Nat × Nat :=
  let ai : Nat := (bitsK mask).foldl
    (fun acc i => (dk.absidx.getD i []).foldl (fun a j => a ||| bitK j) acc) 0
  let cs := compsK dk.aadj ai
  if cs.length > 1 then
    if dk.mode == 1 && cs.length == 2 then
      let c0 := cs.getD 0 0
      let tn := typeNameK (rankQK (toI (rootsOfMaskK dk.AR c0))) (popcK c0)
      (tn.1, false, tn.2, 2)
    else (99, false, 0, 0)
  else
    let c := cs.getD 0 0
    let rts := rootsOfMaskK dk.AR c
    let tn := typeNameK (rankQK (toI rts)) (popcK c)
    let moved : Bool :=
      if dk.mode == 1 then
        rts.any fun r =>
          (!(rts.any fun s => s != r && match subIdx dk.AR r s with
              | some k => hasBitK c k
              | none => false)) && permVecK dk.rho r != r
      else false
    let opp := (tn.1 == 0 && tn.2 ≥ 2) || (tn.1 == 1 && tn.2 % 2 == 1) || (tn.1 == 2 && tn.2 == 6)
    (tn.1, opp != moved, tn.2, 1)

@[expose] def kernelK (dk : DK) (m : Nat) : List (List Nat) :=
  null3K ((bitsK m).map (fK dk)) dk.d

@[expose] def solvableK (dk : DK) (m : Nat) : Bool :=
  let l := labelPureK dk m
  l.1 == 0 && l.2.2.2 == 1 && ((!l.2.1 && l.2.2.1 == 1) || (l.2.1 && l.2.2.1 == 2))

@[expose] def internalK (dk : DK) (c : Nat) (v : List Nat) : Bool :=
  let hs := (rowRed3K ((bitsK c).map (hK dk)) dk.d).1
  rank3K (hs ++ [v]) dk.d == hs.length

@[expose] def clGo (rows : List Nat) : Nat → Nat → List Nat → Nat
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | f + 1, seen, j :: todo =>
    let st := rows.foldl (fun st row =>
      let k := (row >>> (7 * j)) % 128
      if hasBitK st.1 k then st else (st.1 ||| bitK k, k :: st.2)) (seen, todo)
    clGo rows f st.1 st.2

@[expose] def closureK (dk : DK) (ids : List Nat) : Nat :=
  clGo (ids.map fun i => dk.reflP.getD i 0) 256 (ids.foldl (fun m i => m ||| bitK i) 0) ids.reverse

@[expose] def extensionsK (dk : DK) (common X : Nat) : List (Nat × Int) :=
  let ss := simpOfK dk common
  if ss.length + 1 != (kindOfK dk X).2 then [] else
  (bitsK (X ^^^ (X &&& common))).flatMap fun i =>
    ([(1 : Int), -1].filter fun sg =>
      ss.all (fun j => sg * gI dk i j ≤ 0) && closureK dk (ss ++ [i]) == X).map fun sg => (i, sg)

@[expose] def dgGo (C : List (List Int)) (m : Nat) : Nat → Nat → List Nat → Nat
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | f + 1, seen, i :: todo =>
    let st := (List.range m).foldl (fun st j =>
      if !hasBitK st.1 j && i != j && (C.getD i []).getD j 0 != 0 then (st.1 ||| bitK j, j :: st.2)
      else st) (seen, todo)
    dgGo C m f st.1 st.2

@[expose] def diagramK (dk : DK) (V : List (Nat × Int)) : Option (List (List Int) × Int) :=
  let m := V.length
  let C : List (List Int) := V.map fun a => V.map fun b =>
    2 * a.2 * b.2 * gI dk a.1 b.1 / gI dk b.1 b.1
  if (List.range m).any fun i => (List.range m).any fun j => i != j && (C.getD i []).getD j 0 > 0
  then none else
  let dd := detIntK C
  if dd ≤ 0 then none else
  if popcK (dgGo C m (m + 1) 1 [0]) != m then none else
  if ((List.range (m - 1)).filter fun j => (C.getD (m - 1) []).getD j 0 != 0).length != 1 then none
  else some (C, dd)

@[expose] def modelK (dk : DK) (L K : Nat) : Bool × Bool :=
  let common := L &&& K
  let ss : List (Nat × Int) := (simpOfK dk common).map fun i => (i, 1)
  let eL := extensionsK dk common L
  let eK := extensionsK dk common K
  match (eL.flatMap fun b => eK.map fun a => (ss ++ [b]) ++ [a]).find? fun V =>
      (diagramK dk V).isSome with
  | none => (false, false)
  | some V =>
    let idsL := (V.take (V.length - 1)).map (·.1)
    let idsK := (V.take (V.length - 2) ++ [V.getD (V.length - 1) (0, 0)]).map (·.1)
    (true, !((kernelK dk L).length == 1 && (kernelK dk K).length == 1) ||
      (closureK dk idsL != L || closureK dk idsK != K))

@[expose] def ambTry (dk : DK) (psi : Nat) (V : List (Nat × Int)) :
    Option (List (Nat × Int) × Int × Int) :=
  match diagramK dk V with
  | none => none
  | some (C, dd) =>
    if dd % 3 == 0 || V.length != dk.d then none else
    let dl := detIntK ((C.take (C.length - 1)).map fun r => r.take (r.length - 1))
    if dl % 3 == 0 then none else
    if closureK dk (V.map (·.1)) != psi then none else some (V, dd, dl)

@[expose] def ambientK (dk : DK) (J L K : Nat) : Option ((Nat × Nat) × Int × Int) × Bool :=
  let psi := closureK dk (bitsK (L ||| K))
  let tries := (extensionsK dk J L).flatMap fun b =>
    let ss := (simpOfK dk J).map (fun i => (i, (1 : Int))) ++ [b]
    (bitsK (psi ^^^ (psi &&& L))).flatMap fun i => [(1 : Int), -1].map fun sg => ss ++ [(i, sg)]
  match tries.findSome? (ambTry dk psi) with
  | none => (none, false)
  | some (V, dd, dl) =>
    (some (kindOfK dk psi, dd, dl),
      rank3K (V.map fun v => hK dk v.1) dk.d != dk.d ||
        closureK dk ((V.take (V.length - 1)).map (·.1)) != L)

@[expose] def twonodeK (dk : DK) (X J : Nat) : Bool :=
  let la := labelPureK dk X
  let lb := labelPureK dk J
  let a := la.1
  let atw := la.2.1
  let n := la.2.2.1
  let f := la.2.2.2
  let b := lb.1
  let btw := lb.2.1
  let m := lb.2.2.1
  let g := lb.2.2.2
  let pa := (2 ^ f + 1) % 3 == 0
  let pm := (2 ^ f - 1) % 3 == 0
  f == g && (
    (a == 0 && b == 0 && atw && btw && pa && n == m + 2 && (m + 3) % 3 == 0) ||
    (a == 0 && b == 0 && !atw && !btw && pm && n == m + 2 && (m + 3) % 3 == 0) ||
    (a == 2 && atw && pa && n == 6 && b == 1 && !btw && m == 4) ||
    (a == 2 && !atw && pm && n == 6 && b == 1 && !btw && m == 4))

@[expose] def rowOkK (mode : Nat) (lL lJ lK : Nat × Bool × Nat × Nat) (kL kJ kK : Nat × Nat)
    (w : (Nat × Nat) × Int × Int) : Bool :=
  match mode with
  | 1 => lL == (0, false, 5, 1) && lJ == (0, false, 2, 2) && lK == (0, false, 5, 1) &&
      kL == (4, 3) && kJ == (0, 2) && kK == (4, 3) && w == ((3, 4), 1, 2)
  | 4 => lL == (1, false, 6, 1) && lJ == (0, true, 5, 1) && lK == (1, false, 6, 1) &&
      kL == (1, 6) && kJ == (0, 5) && kK == (1, 6) && w == ((2, 7), 2, 4)
  | 5 => lL == (2, false, 7, 1) && lJ == (2, true, 6, 1) && lK == (2, false, 7, 1) &&
      kL == (2, 7) && kJ == (2, 6) && kK == (2, 7) && w == ((2, 8), 1, 2)
  | _ => false

abbrev Cand := List Nat × Nat × Bool × Bool × Bool × List (List Nat)

@[expose] def dlK (d : Nat) (x y : List Nat) : List (List Nat) :=
  ([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)].map fun (ab : Nat × Nat) =>
    line3K ((List.range d).map fun i => (ab.1 * x.getD i 0 + ab.2 * y.getD i 0) % 3)).foldl
    (fun acc z => if acc.contains z then acc else acc ++ [z]) []

@[expose] def candsAt (dk : DK) (x : List Nat) (zx L J : Nat) (z : List Nat) : List Cand :=
  (compsK dk.adj (zerosK dk z)).filterMap fun K =>
    if (J &&& (K ^^^ dk.full)) != 0 then none
    else if solvableK dk K then none
    else if (K &&& (zx ^^^ dk.full)) == 0 then none
    else
      let kk := kernelK dk K
      if kk.length > 2 then none else
      let md := if kk.length == 1 then modelK dk L K else (false, false)
      let t1 := twonodeK dk L J && !internalK dk L x
      let t2 := twonodeK dk K J && !internalK dk K z
      some (z, K, md.1, t1 || t2, md.2, kk)

@[expose] def aEnt (i : Nat) : List (List Nat) → Nat → Nat
  | [], _ => 0
  | v :: vs, c => (c % 3) * v.getD i 0 + aEnt i vs (c / 3)

@[expose] def patternsK (dk : DK) (dual : List (List Nat)) (cands : List Cand) :
    List (List Nat) × Bool :=
  (List.range (3 ^ dual.length)).foldl (fun st code =>
    let a := (List.range dk.d).map fun i => aEnt i dual code % 3
    let nz := a.any (· != 0)
    if dk.d - (if nz then 1 else 0) < 4 then st
    else if nz && line3K a != a then st
    else
      let avail := (List.range cands.length).filter fun j =>
        let kj := ((cands.getD j ([], 0, false, false, false, [])).2.2.2.2.2)
        kj.length == 1 || kj.any fun k => dot3K a k != 0
      let bad := avail.any fun j => ((cands.getD j ([], 0, false, false, false, [])).2.2.2.2.2).length != 1
      (if st.1.contains avail then st.1 else st.1 ++ [avail], st.2 || bad)) ([], false)

@[expose] def residBad (dk : DK) (L J : Nat) (cands : List Cand) (pat : List Nat) : Bool :=
  pat.any fun j =>
    let K := (cands.getD j ([], 0, false, false, false, [])).2.1
    match (ambientK dk J L K) with
    | (none, _) => true
    | (some w, b) =>
      b || !(rowOkK dk.mode (labelPureK dk L) (labelPureK dk J) (labelPureK dk K) (kindOfK dk L)
        (kindOfK dk J) (kindOfK dk K) w)

@[expose] def planeK (dk : DK) (x : List Nat) (zx L w : Nat) (y : List Nat)
    (D : List (List Nat)) : List Nat × List Nat × Bool :=
  let ns := (compsK dk.adj (L &&& zerosK dk y)).filter fun c => !solvableK dk c
  let eligible := ns.filter fun c => (kernelK dk c).length == 2
  if eligible.length == 0 then ([0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0], false) else
  let bad0 := !(ns.length == 1 && eligible.length == 1)
  let J := eligible.getD 0 0
  let cands := ((dlK dk.d x y).filter (· != x)).flatMap (candsAt dk x zx L J)
  let badC := cands.any fun c => c.2.2.2.2.1
  if cands.length == 0 then ([0, 0, 1, 0, 1, 0, 0], [w, 0, w, 0, 0], bad0) else
  if cands.any (fun c => c.2.2.1) then ([0, 0, 1, 1, 0, 0, 0], [w, w, 0, 0, 0], bad0 || badC) else
  let pp := patternsK dk (null3K D dk.d) cands
  let resid := pp.1.filter fun pat => pat.length > 0 && !(pat.any fun j =>
    (cands.getD j ([], 0, false, false, false, [])).2.2.2.1)
  if resid.length == 0 then ([0, 0, 1, 0, 0, 1, 0], [w, 0, 0, w, 0], bad0 || badC || pp.2) else
  ([0, 0, 1, 0, 0, 0, resid.length], [w, 0, 0, 0, resid.length * w],
    bad0 || badC || pp.2 || resid.any (residBad dk L J cands))

@[expose] def addV (a b : List Nat) : List Nat := List.zipWith (· + ·) a b

@[expose] def planeOf (F : List (List Nat)) (c e : Nat) : Nat :=
  (F.zip (List.range F.length)).foldl (fun m p => if p.1.getD c 0 == e then m ||| bitK p.2 else m) 0

@[expose] def zpOkK (dk : DK) : Bool :=
  dk.N < 128 && dk.F.length == dk.N && dk.R.length == dk.N && dk.zp.length == dk.d &&
    (List.range dk.d).all fun c => dk.zp.getD c (0, 0) == (planeOf dk.F c 1, planeOf dk.F c 2)

end Certificates.GilmanCensusK

end
