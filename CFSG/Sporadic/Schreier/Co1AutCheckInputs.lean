module

public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import CFSG.Sporadic.Schreier.Co1AutData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1AutData
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

@[expose] def stabDag : List Rows × List Rows × Bool := dag [hRows0, hRows1] Data.stabDerivs

@[expose] def stabColsT : Array Rows :=
  Array.ofFn (n := 85) fun j => transposeRows 24 (stabDag.1.getD j.val one)

@[expose] def stabTowerCheck : Bool :=
  stabDag.2.2 && stabDag.1.length == 85 &&
    vTowerOK stabColsT Data.stabTowerBase Data.stabTowerGens Data.stabTowerSizes

@[expose] def tauOf (O : VOrbit) (u : Nat) : Nat :=
  if inEnum O 4600 u then stabVec 0 ^^^ u else u

@[expose] def nonlinCheckOf (O OX : VOrbit) : Bool :=
  Data.nonlinVecs.foldl (· ^^^ ·) 0 == stabVec 3 &&
    Data.nonlinVecs.all (fun w => decide (w < 2 ^ 24) && decide (act aR w < 2 ^ 24) &&
      inEnum OX 98280 w && !inEnum O 4600 w && !inEnum O 4600 (act aR w)) &&
    inEnum O 4600 (stabVec 0 ^^^ stabVec 3) &&
    decide (act aR (stabVec 0 ^^^ stabVec 3) < 2 ^ 24) &&
    Data.nonlinVecs.foldl (fun s w => s ^^^ act aR w) 0 == 11752856 &&
    tauOf O (act aR (stabVec 0 ^^^ stabVec 3)) == 15263478

@[expose] def nonlinCheck : Bool := nonlinCheckOf (stabOrb 3) (fullOrb 2)

end Native

end CFSG.Sporadic.Co1Schreier
