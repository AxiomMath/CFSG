module

public import Certificates.Data.CFSGNative.Fi22.Data
public import Certificates.Data.CFSGNative.F3.Conj
public import Certificates.Data.CFSGNative.F3.Sep
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def matA (_ : Unit := ()) : Array V := rowsOf 77 seedA

@[expose] def matB (_ : Unit := ()) : Array V := rowsOf 77 seedB

@[expose] def matBi (_ : Unit := ()) : Array V := powM 77 matB 12

@[expose] def orbitData (_ : Unit) : COrbit := conjBFS 77 matA matA matB matBi 4000

@[expose] def genTables (O : COrbit) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then O.alpha else if z = 2 then O.beta else invT 3510 O.beta

@[expose] def chainLetters (O : COrbit) : Array Table :=
  buildLetters 3510 (genTables O) chainWords

@[expose] def matrixChecks (_ : Unit := ()) : Bool :=
  canonM 77 matA && canonM 77 matB && canonM 77 (idM 77) && canonM 77 (mul 77 matA matB) &&
    eqM 77 (mul 77 matA matA) (idM 77) && eqM 77 (mul 77 matB matBi) (idM 77) &&
    eqM 77 (powM 77 matB 13) (idM 77) && eqM 77 (powM 77 (mul 77 matA matB) 11) (idM 77) &&
    !eqM 77 matA (idM 77) && !eqM 77 matB (idM 77) && !eqM 77 (mul 77 matA matB) (idM 77)

@[expose] def actionChecks (O : COrbit) (chunks : Nat) : Bool :=
  let L := chainLetters O
  let T := chainTrees 3510 L chainBase
  let lv1 := levelLetters L chainBase 1
  let T2 := treeBFS 3510 subRoot L lv1
  O.keys.size == 3510 && O.alpha.size == 3510 && O.beta.size == 3510 &&
    invoOK 3510 O.alpha && invOK 3510 O.beta (invT 3510 O.beta) &&
    sepOK 77 (sepIdx.map fun r => O.keys[r]!) sepTerms sepVec sepK sepP sepTinv sepTree &&
    sepIdx.all (· < 3510) &&
    chainOK 3510 L chainBase chainQ chainQb T chunks &&
    orbitSizes T == [3510, 2816, 1680, 108, 36] &&
    treeOK 3510 subRoot T2 L lv1 && T2.pts.size == 693 &&
    allIn 0 3510 (fun p => p == 0 ||
      (ap T[1]!.pos p < T[1]!.pts.size && ap T[1]!.pts (ap T[1]!.pos p) == p) ||
      (ap T2.pos p < 693 && ap T2.pts (ap T2.pos p) == p))

@[expose] def productChecks (O : COrbit) : Bool :=
  let P1 := mul 77 matA O.keys[1]!
  let P2 := mul 77 matA O.keys[subRoot]!
  canonM 77 P1 && canonM 77 P2 && eqM 77 (powM 77 P1 3) (idM 77) && !eqM 77 P1 (idM 77) &&
    eqM 77 (powM 77 P2 2) (idM 77) && !eqM 77 P2 (idM 77)

@[expose] def fi22Certificate (chunks : Nat) : Bool :=
  matrixChecks &&
    let O := orbitData ()
    conjOrbitOK 77 matA matA matB matBi O chunks && actionChecks O chunks && productChecks O

end CFSG.Sporadic.Fi22.Native
