module

public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import CFSG.Sporadic.Schreier.Co1LiftData
public import CFSG.Sporadic.Co2Cert.Data
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1LiftData
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Co2Cert.Data
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

@[expose] def clsVal (R : Array Nat) (m : Nat) : Nat :=
  if m < 2300 then R[m]! else stabVec 0 ^^^ R[m - 2300]!

@[expose] def inCls (R : Array Nat) (w k : Nat) : Bool :=
  w == clsVal R k || w == clsVal R (k + 2300)

@[expose] def liftCheckOf (R a0 a1 : Array Nat) : Bool :=
  R.size == 2300 &&
    (List.range 4600).all (fun m => decide (clsVal R m < 2 ^ 24)) &&
    vSorted (((List.range 4600).map (clsVal R)).mergeSort fun a b => decide (a ≤ b)) &&
    (List.range 2300).all fun j =>
      inCls R (act hRows0 R[j]!) a0[j]! && inCls R (act hRows1 R[j]!) a1[j]!

@[expose] def liftCheck : Bool :=
  liftCheckOf Data.liftReps.toArray CFSG.Sporadic.Co2Cert.co2OrigArrs[0]!
    CFSG.Sporadic.Co2Cert.co2OrigArrs[1]!

end Native

end CFSG.Sporadic.Co1Schreier
