module

public import Certificates.Data.CFSGNative.McL.Data
public import Certificates.Data.CFSGNative.McL.VecOrbit
public import Certificates.Data.CFSGNative.Perm.Chain
public import Certificates.Data.CFSGNative.F3.Conj

public section

namespace CFSG.Sporadic.McL.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.VecOrbit.Native

set_option compiler.extract_closed false

@[expose] def matA (_ : Unit := ()) : Array V := rowsOf 21 seedA

@[expose] def matB (_ : Unit := ()) : Array V := rowsOf 21 seedB

@[expose] def orbitData (_ : Unit) : VOrbit :=
  vecBFS 21 (transpose 21 matA) (transpose 21 matB) rootVec 400

@[expose] def genTables (O : VOrbit) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then O.alpha else if z = 2 then O.beta else invT 275 O.beta

@[expose] def chainLetters (O : VOrbit) : Array Table :=
  buildLetters 275 (genTables O) chainWords

@[expose] def matrixChecks (_ : Unit := ()) : Bool :=
  canonM 21 matA && canonM 21 matB && canonM 21 (idM 21) && canonM 21 (mul 21 matA matB) &&
    eqM 21 (mul 21 matA matA) (idM 21) && eqM 21 (powM 21 matB 5) (idM 21) &&
    eqM 21 (powM 21 (mul 21 matA matB) 11) (idM 21) &&
    !eqM 21 matA (idM 21) && !eqM 21 matB (idM 21) && !eqM 21 (mul 21 matA matB) (idM 21)

@[expose] def actionChecks (O : VOrbit) (chunks : Nat) : Bool :=
  let L := chainLetters O
  let T := chainTrees 275 L chainBase
  let lv1 := levelLetters L chainBase 1
  let T2 := treeBFS 275 subRoot L lv1
  O.pts.size == 275 && O.alpha.size == 275 && O.beta.size == 275 &&
    invoOK 275 O.alpha && invOK 275 O.beta (invT 275 O.beta) &&
    chainQ.size == 21 && chainQ.all (· < 275) &&
    basisOK 21 (chainQ.map fun r => O.pts[r]!) basisTinv &&
    chainOK 275 L chainBase chainQ chainQb T chunks &&
    orbitSizes T == [275, 162, 56, 30, 4, 3] &&
    treeOK 275 subRoot T2 L lv1 && T2.pts.size == 112 &&
    allIn 0 275 (fun p => p == 0 ||
      (ap T[1]!.pos p < T[1]!.pts.size && ap T[1]!.pts (ap T[1]!.pos p) == p) ||
      (ap T2.pos p < 112 && ap T2.pts (ap T2.pos p) == p))

@[expose] def mclCertificate (chunks : Nat) : Bool :=
  matrixChecks &&
    let O := orbitData ()
    vecOrbitOK 21 (transpose 21 matA) (transpose 21 matB) O chunks && actionChecks O chunks

end CFSG.Sporadic.McL.Native
