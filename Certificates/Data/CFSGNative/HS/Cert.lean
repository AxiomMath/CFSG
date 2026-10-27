module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.SmallF2.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

structure VecData where
  d : Nat
  seedA : String
  seedB : String
  expA : Nat
  expB : Nat
  v0 : Nat
  n : Nat
  basis : Array Nat
  basisInv : Array Nat
  w0 : List Int
  w1 : List Int
  nregs : Nat
  prog : List Instr
  sel : Array Nat
  base : Array Nat
  qb : Array Nat
  orbSizes : List Nat
  subReps : Array Nat
  subSizes : List Nat
  ord0 : Nat × Nat
  ord1 : Nat × Nat
  ord01 : Nat × Nat

namespace VecData

variable (D : VecData)

@[expose] def rowsA : Array Nat := rowsOfPayload D.d D.seedA

@[expose] def rowsB : Array Nat := rowsOfPayload D.d D.seedB

@[expose] def colsA : Array Nat := transposeRows D.d D.rowsA

@[expose] def colsB : Array Nat := transposeRows D.d D.rowsB

@[expose] def orbit (_ : Unit) : VOrbit := vOrbitBFS D.d D.colsA D.colsB D.v0 D.n

end VecData

@[expose] def genT (n : Nat) (O : VOrbit) (z : Int) : Table :=
  if z = 1 then O.alpha else if z = -1 then invT n O.alpha else if z = 2 then O.beta
  else invT n O.beta

@[expose] def regs0 (D : VecData) (O : VOrbit) : Array Table :=
  Array.ofFn (n := D.nregs) fun r =>
    if r.val = 0 then wordT D.n (genT D.n O) D.w0 else if r.val = 1 then wordT D.n (genT D.n O) D.w1
    else idT D.n

@[expose] def lettersOf (n : Nat) (sel : Array Nat) (R : Array Table) : Array Table :=
  Array.ofFn (n := 2 * sel.size) fun i =>
    if i.val % 2 = 0 then R[sel[i.val / 2]!]! else invT n R[sel[i.val / 2]!]!

@[expose] def instrLt (r : Nat) : Instr → Bool
  | .mu i j k => decide (i < r) && decide (j < r) && decide (k < r)
  | .pwr _ i k => decide (i < r) && decide (k < r)
  | .iv i k => decide (i < r) && decide (k < r)

@[inline, expose] def inTreeB (T : Tree) (p : Nat) : Bool :=
  decide (ap T.pos p < T.pts.size) && ap T.pts (ap T.pos p) == p

@[expose] def labelsOf (n : Nat) (subT : Array Tree) : Array Nat := Id.run do
  let mut labs : Array Nat := Array.replicate n 0
  for j in [0:subT.size] do
    let T := subT[j]!
    for k in [0:T.pts.size] do
      labs := labs.set! (ap T.pts k) j
  return labs

@[expose] def ordOK (n : Nat) (Q : Array Nat) (T : Table) (pe : Nat × Nat) : Bool :=
  decide (0 < pe.2) && tupleEq (apT (powT n (pe.1 ^ pe.2) T) Q) Q &&
    !tupleEq (apT (powT n (pe.1 ^ (pe.2 - 1)) T) Q) Q

@[expose] def baseChecks (D : VecData) (O : VOrbit) : Bool :=
  decide (0 < D.d) && decide (D.d < 64) && decide (0 < D.expA) && decide (0 < D.expB) &&
    powRows D.d D.rowsA D.expA == idRows D.d && powRows D.d D.rowsB D.expB == idRows D.d &&
    vOrbitOK D.d D.n D.colsA D.colsB O && decide (D.n < 2 ^ 30) &&
    invOK D.n O.alpha (invT D.n O.alpha) && invOK D.n O.beta (invT D.n O.beta) &&
    D.basis.size == D.d && D.basis.all (· < D.n) &&
    mulRows D.d D.basisInv (D.basis.map fun i => O.pts[i]!) == idRows D.d

@[expose] def chainChecks (D : VecData) (O : VOrbit) (ok : Bool) (L : Array Table)
    (T : Array Tree) (chunks : Nat) : Bool :=
  decide (2 ≤ D.nregs) && D.prog.all (instrLt D.nregs) && ok && D.sel.all (· < D.nregs) &&
    chainOK D.n L D.base D.basis D.qb T chunks && orbitSizes T == D.orbSizes &&
    sift T L D.qb D.basis 0 (apT O.alpha D.basis) &&
    sift T L D.qb D.basis 0 (apT O.beta D.basis)

@[expose] def subChecks (D : VecData) (L : Array Table) (lv : Array Nat) (S : Array Tree) :
    Bool :=
  let k := D.subReps.size
  let labs := labelsOf D.n S
  decide (0 < D.base.size) && D.base[0]! == 0 && decide (0 < k) && D.subReps[0]! == 0 &&
    S.size == k && (S.toList.map fun T => T.pts.size) == D.subSizes &&
    allIn 0 k (fun j => treeOK D.n D.subReps[j]! S[j]! L lv) &&
    allIn 0 D.n (fun p => decide (labs[p]! < k) && inTreeB S[labs[p]!]! p) &&
    allIn 0 k (fun j => allIn 0 S[j]!.pts.size fun t => labs[ap S[j]!.pts t]! == j)

@[expose] def ordChecks (D : VecData) (R0 : Array Table) : Bool :=
  ordOK D.n D.basis R0[0]! D.ord0 && ordOK D.n D.basis R0[1]! D.ord1 &&
    ordOK D.n D.basis (compT D.n R0[0]! R0[1]!) D.ord01

@[expose] def vecCert (D : VecData) (chunks : Nat) : Bool :=
  let O := D.orbit ()
  let R0 := regs0 D O
  let st := runSLP D.n D.prog R0
  let L := lettersOf D.n D.sel st.1
  let T := chainTrees D.n L D.base
  let lv := levelLetters L D.base 1
  let S := D.subReps.map fun r => treeBFS D.n r L lv
  baseChecks D O && chainChecks D O st.2 L T chunks && subChecks D L lv S && ordChecks D R0

end CFSG.Sporadic.SmallF2.Native
