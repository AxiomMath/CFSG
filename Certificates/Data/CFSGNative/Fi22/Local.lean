module

public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.CFSGNative.Fi22.LocalData
public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F4.Native

set_option compiler.extract_closed false

@[expose] def t46Gen (z : Int) : Table := tvTable tvGens[z.natAbs - 1]!

@[expose] def t46Letters (_ : Unit := ()) : Array Table := buildLetters 693 t46Gen t46Words

@[expose] def t46Q (_ : Unit := ()) : Array Nat := Array.range 693

@[expose] def t46Trees (_ : Unit := ()) : Array Tree := chainTrees 693 t46Letters t46Base

@[expose] def eaPts (O : COrbit) : Array Nat :=
  ((List.range 3510).filter fun k => k != 0 && ap O.alpha k == k).toArray

@[expose] def eaPos (O : COrbit) : Array Nat := Id.run do
  let e := eaPts O
  let mut r : Array Nat := Array.replicate 3510 693
  for i in [0:e.size] do
    r := r.set! e[i]! i
  return r

@[expose] def phiInv (_ : Unit := ()) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate 693 693
  for i in [0:phiData.size] do
    r := r.set! phiData[i]! i
  return r

@[expose] def conjTables (O : COrbit) : Array Table := Id.run do
  let bi := invT 3510 O.beta
  let mut T : Array Table := #[O.alpha]
  for k in [1:3510] do
    let p := ap O.par k
    let t := if ap O.lab k == 1 then compT 3510 (compT 3510 O.alpha T[p]!) O.alpha
      else compT 3510 (compT 3510 O.beta T[p]!) bi
    T := T.push t
  return T

@[expose] def restrictRename (e p : Array Nat) (L : Table) : Array Nat :=
  Array.ofFn (n := 693) fun u => phiData[p[ap L e[phiInv[u.val]!]!]!]!

@[expose] def restrictOK (e p : Array Nat) (L : Table) : Bool :=
  allIn 0 693 fun i => p[ap L e[i]!]! < 693

@[expose] def letterChecks (e p : Array Nat) (L : Array Table) (lv1 : Array Nat) : Bool :=
  lv1.all fun l => restrictOK e p L[l]! &&
    sift t46Trees t46Letters t46Base t46Q 0 (restrictRename e p L[l]!)

@[expose] def tvChecks (e p : Array Nat) (CT : Array Table) : Bool :=
  allIn 0 693 fun i =>
    let tv := tvTable uPts[phiData[i]!]!
    let T := CT[e[i]!]!
    allIn 0 693 fun j => phiData[p[ap T e[j]!]!]! == ap tv phiData[j]!

@[expose] def eaChecks (e : Array Nat) : Bool :=
  e.size == 693 && phiData.size == 693 && allIn 0 693 (fun i => phiData[i]! < 693) &&
    allIn 0 693 (fun u => phiInv[u]! < 693 && phiData[phiInv[u]!]! == u)

@[expose] def fi22LocalChecks (O : COrbit) : Bool :=
  eaChecks (eaPts O) &&
    letterChecks (eaPts O) (eaPos O) (chainLetters O)
      (levelLetters (chainLetters O) chainBase 1) &&
    tvChecks (eaPts O) (eaPos O) (conjTables O)

@[expose] def localCertificate (chunks : Nat) : Bool :=
  uPtsOK &&
    chainOK 693 t46Letters t46Base t46Q t46Base t46Trees chunks &&
    orbitSizes t46Trees == [693, 512, 120, 36, 6] &&
    fi22LocalChecks (orbitData ())

end CFSG.Sporadic.Fi22.Native
