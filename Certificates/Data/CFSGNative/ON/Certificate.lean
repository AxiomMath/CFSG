module

public import Certificates.Data.CFSGNative.ON.Basic
public import Certificates.Data.CFSGNative.ON.Data

public section

namespace CFSG.Sporadic.ON.Native

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt ordOK inTreeB labelsOf)

set_option compiler.extract_closed false

abbrev nPts (_ : Unit := ()) : Nat := 245520

abbrev nLines (_ : Unit := ()) : Nat := 122760

@[expose] def rowsA (_ : Unit := ()) : Array V := rowsOf 154 seedA

@[expose] def rowsB (_ : Unit := ()) : Array V := rowsOf 154 seedB

@[expose] def colsA (_ : Unit := ()) : Array W := (transpose 154 rowsA).map ofV

@[expose] def colsB (_ : Unit := ()) : Array W := (transpose 154 rowsB).map ofV

@[expose] def rootW (_ : Unit := ()) : W :=
  ofV (V.ofFn 154 fun j => (rootDigits.toList.getD j '0').toNat - '0'.toNat)

@[expose] def orbitData (_ : Unit) : VOrbit := orbitBFS colsA colsB rootW nPts

@[expose] def matrixChecks (_ : Unit := ()) : Bool :=
  eqM 154 (mul 154 rowsA rowsA) (idM 154) && eqM 154 (powM 154 rowsB 4) (idM 154)

@[expose] def genT (O : VOrbit) (z : Int) : Table :=
  if z = 1 then O.alpha else if z = -1 then invT nPts O.alpha else if z = 2 then O.beta
  else invT nPts O.beta

@[expose] def regs0 (O : VOrbit) : Array Table :=
  Array.ofFn (n := nregs) fun r =>
    if r.val = 0 then wordT nPts (genT O) wordA else if r.val = 1 then wordT nPts (genT O) wordB
    else idT nPts

@[expose] def basisRows (O : VOrbit) : Array W := chainQ.map fun i => O.keys[i]!

@[expose] def coefs (X : Array W) (w : W) : W := combW 154 X w

@[expose] def lineReps (N : Table) : Table := Id.run do
  let mut r : Table := #[]
  for k in [0:nPts] do
    if k < ap N k then r := r.push (UInt32.ofNat k)
  return r

@[expose] def lineOfT (N R : Table) : Table := Id.run do
  let mut t : Table := Array.replicate nPts 0
  for j in [0:R.size] do
    let k := ap R j
    t := (t.set! k (UInt32.ofNat j)).set! (ap N k) (UInt32.ofNat j)
  return t

@[expose] def lineLetters (L : Array Table) (R Lf : Table) : Array Table :=
  L.map fun T => Array.ofFn (n := nLines) fun j => Lf[(T[(R[j.val]!).toNat]!).toNat]!

@[expose] def subTreesOf (LL : Array Table) (lv : Array Nat) : Array Tree :=
  subRoots.map fun r => treeBFS nLines r LL lv

@[expose] def basisChecks (Rb X : Array W) : Bool :=
  chainQ.size == 154 && chainQ.all (· < nPts) && X.size == 154 && X.all W.wf &&
    decide (mulW 154 X Rb = idW 154)

@[expose] def chainChecks (O : VOrbit) (N : Table) (ok : Bool) (L : Array Table) (T : Array Tree)
    (chunks : Nat) : Bool :=
  prog.all (instrLt nregs) && ok && sel.all (· < nregs) &&
    invOK nPts O.alpha (invT nPts O.alpha) && invOK nPts O.beta (invT nPts O.beta) &&
    chainOK nPts L chainBase chainQ chainQb T chunks && orbitSizes T == orbSizes &&
    sift T L chainQb chainQ 0 (apT O.alpha chainQ) &&
    sift T L chainQb chainQ 0 (apT O.beta chainQ) &&
    !sift T L chainQb chainQ 0 (apT N chainQ)

@[expose] def lineChecks (N R Lf : Table) : Bool :=
  ap Lf 0 == 0 && allIn 0 nLines (fun j => ap R j < nPts && ap Lf (ap R j) == j) &&
    allIn 0 nPts (fun k => ap Lf k < nLines && ap Lf (ap N k) == ap Lf k &&
      (ap R (ap Lf k) == k || ap R (ap Lf k) == ap N k))

@[expose] def subChecks (LL : Array Table) (lv : Array Nat) (S : Array Tree) (labs : Array Nat) :
    Bool :=
  S.size == 5 && subRoots.size == 5 && subRoots[0]! == 0 &&
    allIn 0 5 (fun i => CFSG.Perm.Native.treeOK nLines subRoots[i]! S[i]! LL lv &&
      allIn 0 S[i]!.pts.size (fun k => labs[ap S[i]!.pts k]! == i)) &&
    allIn 0 nLines (fun p => decide (labs[p]! < 5) && inTreeB S[labs[p]!]! p) &&
    (S.toList.map fun T => T.pts.size) == subSizes

@[expose] def supportChecks (O : VOrbit) (Rb X : Array W) : Bool :=
  checkVecs.all (· < nPts) &&
    checkVecs.all (fun c => decide (combW 154 Rb (coefs X O.keys[c]!) = O.keys[c]!) &&
      ((coefs X O.keys[c]!).bitP 0 || (coefs X O.keys[c]!).bitM 0)) &&
    allIn 0 154 (fun t =>
      checkVecs.any fun c => (coefs X O.keys[c]!).bitP t || (coefs X O.keys[c]!).bitM t)

@[expose] def ordChecks (R0 : Array Table) : Bool :=
  ordOK nPts chainQ R0[0]! (2, 1) && ordOK nPts chainQ R0[1]! (19, 1) &&
    ordOK nPts chainQ (compT nPts R0[0]! R0[1]!) (11, 1)

@[expose] def onCertificate (chunks : Nat) : Bool :=
  let O := orbitData ()
  let index := indexOf O.keys
  let pos : W → Nat := fun x => index.getD x nPts
  let N := negTable O pos
  let Rb := basisRows O
  let X := invW 154 Rb
  let R0 := regs0 O
  let st := runSLP nPts prog R0
  let L := lettersOf nPts sel st.1
  let T := chainTrees nPts L chainBase
  let reps := lineReps N
  let Lf := lineOfT N reps
  let LL := lineLetters L reps Lf
  let lv := levelLetters L chainBase 1
  let S := subTreesOf LL lv
  let labs := labelsOf nLines S
  matrixChecks && orbitOK nPts colsA colsB O pos chunks && negOK nPts O N &&
    basisChecks Rb X && chainChecks O N st.2 L T chunks && lineChecks N reps Lf &&
    subChecks LL lv S labs && supportChecks O Rb X && ordChecks R0

end CFSG.Sporadic.ON.Native
