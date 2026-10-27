module

public import Certificates.Data.CFSGNative.Suz.Data
public import Certificates.Data.CFSGNative.Suz.W64
public import Certificates.Data.CFSGNative.F3.Conj
public import Certificates.Data.CFSGNative.F3.Sep
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.Suz.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def matA (_ : Unit := ()) : Array V := rowsOf 64 seedA

@[expose] def matB (_ : Unit := ()) : Array V := rowsOf 64 seedB

@[expose] def wA (_ : Unit := ()) : Array W := matA.map ofV

@[expose] def wB (_ : Unit := ()) : Array W := matB.map ofV

@[expose] def wBi (_ : Unit := ()) : Array W := mulW 64 wB wB

@[expose] def wRoot (_ : Unit := ()) : Array W := rootRows.map ofV

@[expose] def orbitData (_ : Unit) : WOrbit := conjBFSW 64 wRoot wA wA wB wBi 1000 3

@[expose] def genTables (O : WOrbit) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then O.alpha else if z = 2 then O.beta else invT 22880 O.beta

@[expose] def chainLetters (O : WOrbit) : Array Table :=
  buildLetters 22880 (genTables O) chainWords

@[expose] def matrixChecks (_ : Unit := ()) : Bool :=
  canonM 64 matA && canonM 64 matB && canonM 64 (idM 64) && canonM 64 (mul 64 matA matB) &&
    eqM 64 (mul 64 matA matA) (idM 64) && eqM 64 (powM 64 matB 3) (idM 64) &&
    eqM 64 (powM 64 (mul 64 matA matB) 13) (idM 64) &&
    !eqM 64 matA (idM 64) && !eqM 64 matB (idM 64) && !eqM 64 (mul 64 matA matB) (idM 64)

@[expose] def diagD (_ : Unit := ()) : Array V :=
  Array.ofFn (n := 64) fun i => V.ofFn 64 fun j => if j = i.val then formD[i.val]! else 0

@[expose] def formChecks (_ : Unit := ()) : Bool :=
  wfM formF && wfM formP && wfM formPinv && formF.size == 64 && formP.size == 64 &&
    formPinv.size == 64 &&
    eqM 64 (mul 64 (transpose 64 matA) (mul 64 formF matA)) formF &&
    eqM 64 (mul 64 (transpose 64 matB) (mul 64 formF matB)) formF &&
    eqM 64 (mul 64 (transpose 64 formP) (mul 64 formF formP)) diagD &&
    eqM 64 (mul 64 formPinv formP) (idM 64)

@[inline, expose] def inT (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def actionChecks (O : WOrbit) (chunks : Nat) : Bool :=
  let L := chainLetters O
  let T := chainTrees 22880 L chainBase
  let lv1 := levelLetters L chainBase 1
  let T2 := treeBFS 22880 subRoots[0]! L lv1
  let T3 := treeBFS 22880 subRoots[1]! L lv1
  let T4 := treeBFS 22880 subRoots[2]! L lv1
  O.keys.size == 22880 && O.alpha.size == 22880 && O.beta.size == 22880 &&
    invOK 22880 O.beta (invT 22880 O.beta) &&
    sepOK 64 (sepIdx.map fun r => toVM O.keys[r]!) sepTerms sepVec sepK sepP sepTinv sepTree &&
    sepIdx.all (· < 22880) &&
    chainOK 22880 L chainBase chainQ chainQb T chunks &&
    orbitSizes T == [22880, 8505, 144, 16] &&
    treeOK 22880 subRoots[0]! T2 L lv1 && T2.pts.size == 13608 &&
    treeOK 22880 subRoots[1]! T3 L lv1 && T3.pts.size == 280 &&
    treeOK 22880 subRoots[2]! T4 L lv1 && T4.pts.size == 486 &&
    allIn 0 22880 (fun p => p == 0 || inT T[1]! p || inT T2 p || inT T3 p || inT T4 p)

@[expose] def suzCertificate (chunks : Nat) : Bool :=
  matrixChecks && formChecks &&
    let O := orbitData ()
    conjOrbitOKW 64 wRoot wA wA wB wBi O chunks && actionChecks O chunks

end CFSG.Sporadic.Suz.Native
