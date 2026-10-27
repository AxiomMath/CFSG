module

public import Certificates.Data.CFSGNative.J3.Basic
public import Certificates.Data.CFSGNative.Perm.Chain
public import Certificates.Data.CFSGNative.Fi23.Slp

public section

namespace CFSG.Sporadic.J3.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

structure Data where
  seedA : String
  seedB : String
  v0 : Nat
  n : Nat
  words : Array (List Int)
  base : Array Nat
  basis : Array Nat
  qb : Array Nat
  basisInv : Array Nat
  orbSizes : List Nat
  subReps : Array Nat
  derivs : Array (List (Nat × Nat))

@[expose] def genT (n : Nat) (tA tB : Table) (z : Int) : Table :=
  if z = 1 then tA else if z = -1 then invT n tA else if z = 2 then tB else invT n tB

@[inline, expose] def inTreeB (T : Tree) (p : Nat) : Bool :=
  decide (ap T.pos p < T.pts.size) && ap T.pts (ap T.pos p) == p

@[expose] def labelsOf (n : Nat) (S : Array Tree) : Array Nat := Id.run do
  let mut labs : Array Nat := Array.replicate n 0
  for j in [0:S.size] do
    let T := S[j]!
    for k in [0:T.pts.size] do
      labs := labs.set! (ap T.pts k) j
  return labs

@[expose] def invLabel (T : Tree) (L : Array Table) (labs : Array Nat) (k y : Nat) : Nat :=
  labs[(walkInv T L k #[y])[0]!]!

@[expose] def derivStep (n : Nat) (T : Tree) (L : Array Table) (reps labs : Array Nat)
    (D : Array Bool) (st : Nat × Nat) : Array Bool :=
  if decide (st.1 < reps.size) && decide (st.2 < n) && D[st.1]! && D[labs[st.2]!]! then
    D.set! (invLabel T L labs (ap T.pos reps[st.1]!) st.2) true
  else D

@[expose] def derivOK (n k : Nat) (T : Tree) (L : Array Table) (reps labs : Array Nat) (c : Nat)
    (steps : List (Nat × Nat)) : Bool :=
  let D := steps.foldl (derivStep n T L reps labs)
    (((Array.replicate k false).set! 0 true).set! c true)
  allIn 0 k fun j => D[j]!

namespace Data

variable (D : Data)

@[expose] def rowsA : Array Nat := rowsOfPayload 80 D.seedA

@[expose] def rowsB : Array Nat := rowsOfPayload 80 D.seedB

@[expose] def colsA : Array Nat := transposeRows 80 D.rowsA

@[expose] def colsB : Array Nat := transposeRows 80 D.rowsB

@[expose] def pts : Array Nat := orbitSorted 80 D.colsA D.colsB D.v0 D.n

@[expose] def tA : Table := imageTable 80 (posMap D.pts) D.pts D.colsA

@[expose] def tB : Table := imageTable 80 (posMap D.pts) D.pts D.colsB

@[expose] def letters : Array Table := CFSG.Sporadic.Fi23.Native.slpLetters D.n (genT D.n D.tA D.tB) D.words

@[expose] def trees : Array Tree := chainTrees D.n D.letters D.base

@[expose] def lv : Array Nat := levelLetters D.letters D.base 1

@[expose] def subTrees : Array Tree := D.subReps.map fun r => treeBFS D.n r D.letters D.lv

@[expose] def labs : Array Nat := labelsOf D.n D.subTrees

end Data

@[expose] def matOK (rA rB : Array Nat) : Bool :=
  powRows 80 rA 2 == idRows 80 && powRows 80 rB 3 == idRows 80 &&
    powRows 80 (mulRows 80 rA rB) 19 == idRows 80

@[expose] def orbitChecks (D : Data) (cA cB pts : Array Nat) (tA tB : Table) : Bool :=
  orbitOK 80 D.n cA cB pts tA tB && decide (0 < D.n) && decide (D.n < 2 ^ 30) &&
    invOK D.n tA (invT D.n tA) && invOK D.n tB (invT D.n tB) &&
    ap tA 0 != 0 && ap tB 0 != 0 && ap tA (ap tB 0) != 0 &&
    D.basis.size == 80 && D.basis.all (· < D.n) &&
    mulRows 80 D.basisInv (D.basis.map fun i => pts[i]!) == idRows 80

@[expose] def chainChecks (D : Data) (L : Array Table) (T : Array Tree) (chunks : Nat) : Bool :=
  CFSG.Sporadic.Fi23.Native.slpOK D.words && decide (2 ≤ D.words.size) &&
    D.words[0]! == [1] && D.words[1]! == [2] &&
    chainOK D.n L D.base D.basis D.qb T chunks && orbitSizes T == D.orbSizes

@[expose] def subChecks (D : Data) (L : Array Table) (lv : Array Nat) (S : Array Tree)
    (labs : Array Nat) : Bool :=
  let k := D.subReps.size
  decide (0 < D.base.size) && D.base[0]! == 0 && decide (0 < k) && D.subReps[0]! == 0 &&
    S.size == k && S[0]!.pts.size == 1 &&
    allIn 0 k (fun j => treeOK D.n D.subReps[j]! S[j]! L lv) &&
    allIn 0 D.n (fun p => decide (labs[p]! < k) && inTreeB S[labs[p]!]! p) &&
    allIn 0 k (fun j => allIn 0 S[j]!.pts.size fun t => labs[ap S[j]!.pts t]! == j)

@[expose] def derivChecks (D : Data) (L : Array Table) (T0 : Tree) (labs : Array Nat) : Bool :=
  allIn 1 D.subReps.size fun c =>
    derivOK D.n D.subReps.size T0 L D.subReps labs c D.derivs[c]!

@[expose] def check (D : Data) (chunks : Nat) : Bool :=
  let rA := D.rowsA
  let rB := D.rowsB
  let cA := transposeRows 80 rA
  let cB := transposeRows 80 rB
  let pts := orbitSorted 80 cA cB D.v0 D.n
  let pm := posMap pts
  let tA := imageTable 80 pm pts cA
  let tB := imageTable 80 pm pts cB
  let L := CFSG.Sporadic.Fi23.Native.slpLetters D.n (genT D.n tA tB) D.words
  let T := chainTrees D.n L D.base
  let lv := levelLetters L D.base 1
  let S := D.subReps.map fun r => treeBFS D.n r L lv
  let labs := labelsOf D.n S
  matOK rA rB && orbitChecks D cA cB pts tA tB && chainChecks D L T chunks &&
    subChecks D L lv S labs && derivChecks D L T[0]! labs

end CFSG.Sporadic.J3.Native
