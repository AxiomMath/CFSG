module

public import CFSG.Sporadic.Schreier.Co1OddData
public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Co1.Module.InvData
public import Certificates.Data.CFSGNative.Co1.Odd
public meta import CFSG.Sporadic.Schreier.Co1OddData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

@[expose] def oddReg (R : Array (Array Nat)) (i : Nat) : Array Nat := R[i]?.getD (idRows 24)

@[expose] def oddACRegs : Array (Array Nat) := runRows #[hRows0, hRows1] Data.oddACProg

@[expose] def oddCountFix (O : VOrbit) (n : Nat) (Ms : List (Array Nat)) : Nat :=
  countBelow (fun i => Ms.all fun Mt => isFixedN Mt (O.pts[i]!)) n 0

@[expose] def oddACCheckOf (R : Array (Array Nat)) : Bool :=
  validRows (oddReg R 3) && validRows (oddReg R 10) &&
    mulRows 24 (oddReg R 3) (oddReg R 3) == idRows 24 && oddReg R 3 != idRows 24 &&
    mulRows 24 (oddReg R 8) (oddReg R 3) == mulRows 24 (oddReg R 3) (oddReg R 8) &&
    powRows 24 (oddReg R 8) 15 == idRows 24 &&
    mulRows 24 (oddReg R 10) (oddReg R 10) == idRows 24 && oddReg R 10 != idRows 24 &&
    mulRows 24 (oddReg R 15) (oddReg R 10) == mulRows 24 (oddReg R 10) (oddReg R 15) &&
    mulRows 24 (oddReg R 20) (oddReg R 10) == mulRows 24 (oddReg R 10) (oddReg R 20) &&
    powRows 24 (oddReg R 15) 3 == idRows 24 && powRows 24 (oddReg R 20) 3 == idRows 24

@[expose] def oddACCountsOf (R : Array (Array Nat)) : Bool :=
  CFSG.Sporadic.Co1.Module.countsOK (oddReg R 3) 65536 30720 &&
    CFSG.Sporadic.Co1.Module.countsOK (oddReg R 10) 4096 2048

@[expose] def oddACXOf (O : VOrbit) (R : Array (Array Nat)) : Bool :=
  oddCountFix O 98280 [transposeRows 24 (oddReg R 3)] == 2280 &&
    oddCountFix O 98280 [transposeRows 24 (oddReg R 3), transposeRows 24 (oddReg R 8)] == 1 &&
    oddCountFix O 98280 [transposeRows 24 (oddReg R 10)] == 264 &&
    oddCountFix O 98280 [transposeRows 24 (oddReg R 10), transposeRows 24 (oddReg R 15),
      transposeRows 24 (oddReg R 20)] == 2

end Native

end CFSG.Sporadic.Co1Schreier
