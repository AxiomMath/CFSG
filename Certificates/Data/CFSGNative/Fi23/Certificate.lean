module

public import Certificates.Data.CFSGNative.Fi23.Data
public import Certificates.Data.CFSGNative.Fi23.Wide
public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.F3.Sep
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def matA (_ : Unit := ()) : Array W := (rowsOf 253 seedA).map ofV

@[expose] def matB (_ : Unit := ()) : Array W := (rowsOf 253 seedB).map ofV

@[expose] def matBi (_ : Unit := ()) : Array W := mulW 253 matB matB

@[expose] def matE (_ : Unit := ()) : Array W := prodW 253 #[matA, matB] eWord

@[expose] def matD (_ : Unit := ()) : Array W := powW 253 (prodW 253 #[matA, matB] dWord) 7

@[expose] def orbitData (_ : Unit) : WOrbit := conjBFSW 253 matD matA matA matB matBi 200 3

@[expose] def genTables (O : WOrbit) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then O.alpha else if z = 2 then O.beta else invT 31671 O.beta

@[expose] def chainLetters (O : WOrbit) : Array Table :=
  slpLetters 31671 (genTables O) chainWords

@[expose] def isIdT (T : Table) : Bool := allIn 0 31671 fun i => ap T i == i

@[expose] def matrixChecks (_ : Unit := ()) : Bool :=
  canonW 253 matA && canonW 253 matB && canonW 253 (idW 253) && canonW 253 matD &&
    eqW 253 (mulW 253 matA matA) (idW 253) && eqW 253 (mulW 253 matB matBi) (idW 253) &&
    eqW 253 (powW 253 matE 5) (idW 253) && eqW 253 (mulW 253 matD matD) (idW 253) &&
    !eqW 253 matA (idW 253) && !eqW 253 matB (idW 253) && !eqW 253 matD (idW 253)

@[inline, expose] def inTreeB (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def actionChecks (O : WOrbit) (chunks : Nat) : Bool :=
  let L := chainLetters O
  let T := chainTrees 31671 L chainBase
  let lv1 := levelLetters L chainBase 1
  let T2 := treeBFS 31671 subRoot L lv1
  let Y := L[2]!
  let AY := compT 31671 O.alpha Y
  O.keys.size == 31671 && O.alpha.size == 31671 && O.beta.size == 31671 &&
    invoOK 31671 O.alpha && invOK 31671 O.beta (invT 31671 O.beta) &&
    sepOK 253 (chainQ.map fun r => toVM O.keys[r]!) sepTerms sepVec sepK sepP sepTinv sepTree &&
    chainQ.all (· < 31671) &&
    slpOK chainWords && slpPure chainWords && 2 ≤ chainWords.size &&
    chainWords[0]! == [1] && chainWords[1]! == pairWord &&
    chainOK 31671 L chainBase chainQ chainQb T chunks &&
    orbitSizes T == [31671, 3510, 25344, 288, 1260, 4] &&
    sift T L chainQb chainQ 0 (apT O.beta chainQ) &&
    treeOK 31671 subRoot T2 L lv1 && T2.pts.size == 28160 &&
    allIn 0 31671 (fun p => p == 0 || inTreeB T[1]! p || inTreeB T2 p) &&
    isIdT (powT 31671 17 Y) && !isIdT Y && isIdT (powT 31671 23 AY) && !isIdT AY

@[expose] def productChecks (O : WOrbit) : Bool :=
  let P1 := mulW 253 matD O.keys[1]!
  let P2 := mulW 253 matD O.keys[subRoot]!
  canonW 253 P1 && canonW 253 P2 && eqW 253 (powW 253 P1 2) (idW 253) &&
    !eqW 253 P1 (idW 253) && eqW 253 (powW 253 P2 3) (idW 253) && !eqW 253 P2 (idW 253)

@[expose] def fi23Certificate (chunks : Nat) : Bool :=
  matrixChecks &&
    let O := orbitData ()
    conjOrbitOKW 253 matD matA matA matB matBi O chunks && actionChecks O chunks &&
      productChecks O

end CFSG.Sporadic.Fi23.Native
