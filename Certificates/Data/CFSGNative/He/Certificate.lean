module

public import Certificates.Data.CFSGNative.He.Data
public import Certificates.Data.CFSGNative.He.Orbit
public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.He.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

@[expose] def matA (_ : Unit := ()) : Array (Array Nat) := rowsOf 7 50 seedA

@[expose] def matB (_ : Unit := ()) : Array (Array Nat) := rowsOf 7 50 seedB

@[expose] def orbitData (_ : Unit) : VOrbit := vecBFS 7 50 matA matB rootVec 8330

@[expose] def genTables (O : VOrbit) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then O.alpha else if z = 2 then O.beta else invT 8330 O.beta

@[expose] def chainLetters (O : VOrbit) : Array Table :=
  slpLetters 8330 (genTables O) chainWords

@[expose] def isIdT (T : Table) : Bool := allIn 0 8330 fun i => ap T i == i

@[inline, expose] def inTreeB (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def subTrees (L : Array Table) (lv : Array Nat) : Array Tree :=
  subRoots.map fun r => treeBFS 8330 r L lv

@[expose] def labelsOf (Ts : Array Tree) : Array Nat := Id.run do
  let mut lab : Array Nat := Array.replicate 8330 0
  for i in [0:Ts.size] do
    let T := Ts[i]!
    for k in [0:T.pts.size] do
      lab := lab.set! (ap T.pts k) i
  return lab

@[expose] def matrixChecks (_ : Unit := ()) : Bool :=
  mulM 7 50 matA matA == idM 50 && powM 7 50 matB 7 == idM 50

@[expose] def basisCheck (O : VOrbit) : Bool :=
  let M := colsMat 50 O.keys
  mulM 7 50 M (invM 7 50 M) == idM 50

@[expose] def subChecks (L : Array Table) (lv : Array Nat) (Ts : Array Tree) (labs : Array Nat) :
    Bool :=
  Ts.size == 7 && subRoots.size == 7 && subRoots[0]! == 0 &&
    allIn 0 7 (fun i => treeOK 8330 subRoots[i]! Ts[i]! L lv &&
      allIn 0 Ts[i]!.pts.size (fun k => labs[ap Ts[i]!.pts k]! == i)) &&
    allIn 0 8330 (fun p => labs[p]! < 7 && inTreeB Ts[labs[p]!]! p) &&
    (Ts.toList.map fun T => T.pts.size) == subSizes

@[expose] def actionChecks (O : VOrbit) (chunks : Nat) : Bool :=
  let L := chainLetters O
  let T := chainTrees 8330 L chainBase
  let lv1 := levelLetters L chainBase 1
  let Ts := subTrees L lv1
  let labs := labelsOf Ts
  let W := wordT 8330 (genTables O) witWord
  let AB := compT 8330 O.alpha O.beta
  O.keys.size == 8330 && O.alpha.size == 8330 && O.beta.size == 8330 &&
    invoOK 8330 O.alpha && invOK 8330 O.beta (invT 8330 O.beta) && basisCheck O &&
    slpOK chainWords && 2 ≤ chainWords.size && chainWords[0]! == [1] &&
    chainWords[1]! == [2] &&
    chainOK 8330 L chainBase chainQ chainQb T chunks &&
    orbitSizes T == [8330, 4480, 27, 2, 2] &&
    subChecks L lv1 Ts labs &&
    labs[ap W 0]! == 5 && labs[21]! == 3 && labs[ap W 21]! == 1 && labs[24]! == 4 &&
    labs[ap W 24]! == 3 &&
    !isIdT O.alpha && isIdT (powT 8330 7 O.beta) && !isIdT O.beta &&
    isIdT (powT 8330 17 AB) && !isIdT AB

@[expose] def heCertificate (chunks : Nat) : Bool :=
  matrixChecks &&
    let O := orbitData ()
    vecOrbitOK 7 50 matA matB rootVec O chunks && actionChecks O chunks

end CFSG.Sporadic.He.Native
