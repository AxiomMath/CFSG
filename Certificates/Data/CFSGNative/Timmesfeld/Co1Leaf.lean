module

public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Timmesfeld.Co1Leaf

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native

@[expose] def xorL (l : List Nat) : Nat := l.foldl (· ^^^ ·) 0

@[expose] def xorSel (B : List Nat) (c : Nat) : Nat :=
  (List.range B.length).foldl (fun acc k => if c.testBit k then acc ^^^ B.getD k 0 else acc) 0

@[expose] def lowBit (b : Nat) : Nat := b &&& (b ^^^ (b - 1))

@[expose] def crd (B : List Nat) (v : Nat) : Nat :=
  ((List.range B.length).foldl (fun (st : Nat × Nat) k =>
    let b := B.getD k 0
    if st.1 &&& lowBit b != 0 then (st.1 ^^^ b, st.2 ||| (1 <<< k)) else st) (v, 0)).2

@[expose] def basisOf (vs : List Nat) : List Nat :=
  vs.foldl (fun (B : List Nat) v =>
    let r := B.foldl (fun x b => if x &&& lowBit b != 0 then x ^^^ b else x) v
    if r == 0 then B else
      let lb := lowBit r
      B.map (fun b => if b &&& lb != 0 then b ^^^ r else b) ++ [r]) []

@[expose] def colBasis (X : Rows) : List Nat := basisOf (transposeRows 24 X).toList

@[expose] def zeroR (_ : Unit := ()) : Rows := Array.replicate 24 0

@[expose] def expVecs (p : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | r + 1 => (expVecs p r).flatMap fun e => (List.range p).map fun k => e ++ [k]

@[expose] def eltR (gs : List Rows) (e : List Nat) : Rows :=
  (gs.zip e).foldl (fun acc ge => mul acc (pow ge.1 ge.2)) one

@[expose] def eltsOf (gs : List Rows) : Array Rows := ((expVecs 3 gs.length).map (eltR gs)).toArray

@[expose] def dotp (p : Nat) (a b : List Nat) : Nat := ((a.zip b).map fun xy => xy.1 * xy.2).sum % p

@[expose] def pivotIdx (f : List Nat) : Nat :=
  ((List.range f.length).find? fun i => f.getD i 0 != 0).getD 0

@[expose] def normVecs (p r : Nat) : List (List Nat) :=
  (expVecs p r).filter fun f => f.getD (pivotIdx f) 0 == 1

@[expose] def kerBasis (p : Nat) (f : List Nat) : List (List Nat) :=
  let q := pivotIdx f
  ((List.range f.length).filter (· != q)).map fun j =>
    (List.range f.length).map fun i =>
      if i == j then 1 else if i == q then (p - f.getD j 0 % p) % p else 0

@[expose] def kerElts (p : Nat) (gs : List Rows) (f : List Nat) : List Rows :=
  (kerBasis p f).map (eltR gs)

@[expose] def spanBasis (us : List Nat) : List (Nat × Nat) :=
  (us.zipIdx).foldl (fun (B : List (Nat × Nat)) (ui : Nat × Nat) =>
    let r := B.foldl (fun (x : Nat × Nat) b =>
      if x.1 &&& lowBit b.1 != 0 then (x.1 ^^^ b.1, x.2 ^^^ b.2) else x) (ui.1, 1 <<< ui.2)
    if r.1 == 0 then B else
      let lb := lowBit r.1
      B.map (fun b => if b.1 &&& lb != 0 then (b.1 ^^^ r.1, b.2 ^^^ r.2) else b) ++ [r]) []

@[expose] def solveIn (B : List (Nat × Nat)) (t : Nat) : Option Nat :=
  let r := B.foldl (fun (x : Nat × Nat) b =>
    if x.1 &&& lowBit b.1 != 0 then (x.1 ^^^ b.1, x.2 ^^^ b.2) else x) (t, 0)
  if r.1 == 0 then some r.2 else none

@[expose] def bitsOf (n m : Nat) : List Nat := (List.range n).filter m.testBit

structure LeafData where
  piL : List Nat
  w : Nat
  span : List (List Nat)
  basis : List Nat
deriving Inhabited

@[expose] def sumIdx (els : Array Rows) (l : List Nat) : Rows :=
  l.foldl (fun acc i => add acc (els.getD i one)) (zeroR ())

@[expose] def piSupp (gs : List Rows) (els : Array Rows) : List Nat :=
  let r := gs.length
  let evs := (expVecs 3 r).toArray
  let supp (χ : List Nat) : List Nat :=
    (List.range evs.size).filter fun i => χ.all (· == 0) || dotp 3 χ (evs.getD i []) != 0
  ((List.replicate r 0 :: normVecs 3 r).filter fun χ =>
    let d := (colBasis (sumIdx els (supp χ))).length
    if χ.all (· == 0) then 2 ≤ d else 4 ≤ d).flatMap supp

@[expose] def findW (X : List Nat) (els : Array Rows) (piR : Rows) : Nat :=
  let target := 24 - (colBasis piR).length
  let elT := els.map (transposeRows 24)
  let piT := transposeRows 24 piR
  (X.take 2000).foldl (fun found u =>
    if found != 0 then found else
      let w := u ^^^ vecMulN 24 piT u
      if w != 0 && (basisOf (elT.toList.map fun x => vecMulN 24 x w)).length == target then w
      else 0) 0

@[expose] def leafData (X : List Nat) (gs : List Rows) : LeafData :=
  let els := eltsOf gs
  let piL := piSupp gs els
  let piR := sumIdx els piL
  let w := findW X els piR
  let SB := spanBasis (els.toList.map fun x => act x w)
  let span := (List.range 24).map fun i =>
    bitsOf els.size ((solveIn SB ((1 <<< i) ^^^ act piR (1 <<< i))).getD 0)
  ⟨piL, w, span, colBasis piR⟩

@[expose] def testData (X : List Nat) (piT : Rows) (B : List Nat) : List (Nat × Nat) :=
  X.filterMap fun x =>
    let px := vecMulN 24 piT x
    let c := crd B px
    if px != 0 && xorSel B c == px then some (x ^^^ px, c) else none

@[expose] def levelData (T : List (Nat × Nat)) (j : Nat) : List (Nat × Nat) :=
  T.filter fun xc => Nat.log2 xc.2 == j

@[expose] def imgOf (B : List Nat) (pre : List Nat) (c : Nat) : Nat :=
  (List.range pre.length).foldl
    (fun acc k => if c.testBit k then acc ^^^ xorSel B (pre.getD k 0) else acc) 0

@[expose] def levelOK (xs : Std.HashSet Nat) (B : List Nat) (lev : List (Nat × Nat))
    (pre : List Nat) : Bool :=
  lev.all fun xc => xs.contains (xc.1 ^^^ imgOf B pre xc.2)

@[expose] def dfsStep (xs : Std.HashSet Nat) (B : List Nat) (acc : List (List Nat))
    (lev : List (Nat × Nat)) : List (List Nat) :=
  acc.flatMap fun pre => ((List.range (2 ^ B.length)).map fun c => pre ++ [c]).filter
    (levelOK xs B lev)

@[expose] def survivors (xs : Std.HashSet Nat) (B : List Nat) (levels : List (List (Nat × Nat))) :
    List (List Nat) :=
  levels.foldl (dfsStep xs B) [[]]

@[expose] def muC (cs : List Nat) (c : Nat) : Nat :=
  (List.range cs.length).foldl (fun acc k => if c.testBit k then acc ^^^ cs.getD k 0 else acc) 0

@[expose] def cubeOK (cs : List Nat) : Bool :=
  (List.range cs.length).all fun k => muC cs (muC cs (muC cs (1 <<< k))) == 1 <<< k

@[expose] def gensOK (gs : List Rows) : Bool :=
  gs.all wf && gs.all (fun g => gs.all fun h => mul g h == mul h g) &&
    gs.all fun g => pow g 3 == one

@[expose] def searchOK (X : List Nat) (xs : Std.HashSet Nat) (piR : Rows) (B : List Nat) : Bool :=
  B.isEmpty ||
    (let T := testData X (transposeRows 24 piR) B
     (survivors xs B ((List.range B.length).map (levelData T))).all cubeOK)

@[expose] def leafOK (X : List Nat) (xs : Std.HashSet Nat) (gs : List Rows) (D : LeafData) :
    Bool :=
  let els := eltsOf gs
  let piR := sumIdx els D.piL
  let fw := els.map fun x => act x D.w
  let B := D.basis
  gensOK gs && D.piL.all (· < els.size) && mul piR piR == piR && wf piR &&
    act piR D.w == 0 && D.span.length == 24 && D.span.all (·.all (· < els.size)) &&
    (List.range 24).all (fun i =>
      xorL ((D.span.getD i []).map fun j => fw.getD j 0) == ((1 <<< i) ^^^ act piR (1 <<< i))) &&
    B.all (fun b => decide (b < 2 ^ 24) && act piR b == b) &&
    (List.range 24).all (fun i =>
      decide (crd B (act piR (1 <<< i)) < 2 ^ B.length) &&
        xorSel B (crd B (act piR (1 <<< i))) == act piR (1 <<< i)) &&
    searchOK X xs piR B

@[expose] def leavesOK (X : List Nat) (gss : List (List Rows)) : Bool :=
  let xs := Std.HashSet.ofList X
  X.all (· < 2 ^ 24) && gss.all fun gs => leafOK X xs gs (leafData X gs)

@[expose] def splitOK (F A : List Rows) : Bool :=
  gensOK (F ++ A) && decide ((expVecs 3 A.length).map (eltR A)).Nodup

structure Enum where
  elts : Array Rows
  par : Array Nat
  gen : Array Nat
  next : Array (Array Nat)
deriving Inhabited

@[expose] def enumBFS (gs : List Rows) (cap : Nat) : Enum := Id.run do
  let ga := gs.toArray
  let mut pos : Std.HashMap Rows Nat := (∅ : Std.HashMap Rows Nat).insert one 0
  let mut elts : Array Rows := #[one]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut next : Array (Array Nat) := #[]
  for h in [0:cap] do
    if h < elts.size then
      let x := elts[h]!
      let mut row : Array Nat := #[]
      for j in [0:ga.size] do
        let y := mul x ga[j]!
        match pos.get? y with
        | some k => row := row.push k
        | none =>
          pos := pos.insert y elts.size
          row := row.push elts.size
          elts := elts.push y
          par := par.push h
          gen := gen.push j
      next := next.push row
    else break
  return ⟨elts, par, gen, next⟩

@[expose] def rowsKey (R : Rows) : Nat := R.foldl (fun acc r => acc * 16777216 + r) 0

@[expose] def strictSorted : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictSorted (b :: l)
  | _ => true

@[expose] def enumOK (gs : List Rows) (E : Enum) (N : Nat) : Bool :=
  let ga := gs.toArray
  E.elts.size == N && E.par.size == N && E.gen.size == N && E.next.size == N &&
    E.elts.all wf && E.elts.getD 0 one == one &&
    (List.range N).all (fun k => k == 0 ||
      (decide (E.par.getD k 0 < k) && decide (E.gen.getD k 0 < ga.size) &&
        E.elts.getD k one ==
          mul (E.elts.getD (E.par.getD k 0) one) (ga.getD (E.gen.getD k 0) one))) &&
    (List.range N).all (fun k => (E.next.getD k #[]).size == ga.size &&
      (List.range ga.size).all fun j =>
        decide ((E.next.getD k #[]).getD j 0 < N) &&
          E.elts.getD ((E.next.getD k #[]).getD j 0) one ==
            mul (E.elts.getD k one) (ga.getD j one)) &&
    strictSorted ((E.elts.toList.map rowsKey).mergeSort fun a b => decide (a ≤ b))

@[expose] def fusData (E : Enum) (gs : List Rows) (reps : List Rows) : Array (Nat × Nat) :=
    Id.run do
  let N := E.elts.size
  let mut pos : Std.HashMap Rows Nat := ∅
  for k in [0:N] do
    pos := pos.insert E.elts[k]! k
  let mut res : Array (Nat × Nat) := Array.replicate N (0, 0)
  let mut done : Array Bool := Array.replicate N false
  let ga := gs.toArray
  let gi := ga.map inv
  let ra := reps.toArray
  for i in [0:ra.size] do
    match pos.get? ra[i]! with
    | none => pure ()
    | some k0 =>
      if !done[k0]! then
        done := done.set! k0 true
        res := res.set! k0 (i, 0)
        let mut queue : Array Nat := #[k0]
        let mut qi := 0
        for _ in [0:N] do
          if qi < queue.size then
            let k := queue[qi]!
            qi := qi + 1
            let c := (res[k]!).2
            for j in [0:ga.size] do
              let y := mul (mul ga[j]! E.elts[k]!) gi[j]!
              match pos.get? y with
              | none => pure ()
              | some ky =>
                if !done[ky]! then
                  match pos.get? (mul ga[j]! E.elts[c]!) with
                  | none => pure ()
                  | some kc =>
                    done := done.set! ky true
                    res := res.set! ky (i, kc)
                    queue := queue.push ky
  return res

@[expose] def fusOK (E : Enum) (gs : List Rows) (reps : List Rows) (inE : Rows → Bool) : Bool :=
  let F := fusData E gs reps
  let ra := reps.toArray
  (List.range E.elts.size).all fun k =>
    let q := E.elts.getD k one
    q == one || pow q 3 != one || inE q ||
      (let ic := F.getD k (0, 0)
       decide (ic.1 < ra.size) && decide (ic.2 < E.elts.size) &&
         mul q (E.elts.getD ic.2 one) == mul (E.elts.getD ic.2 one) (ra.getD ic.1 one))

end Timmesfeld.Co1Leaf

end
