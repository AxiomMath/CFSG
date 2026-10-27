module

public import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public import Certificates.Data.CFSGNative.Co1.Data
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

@[expose] def fullRoot (k : Nat) : Nat := [0, 1, 2, 4096].getD k 0

@[expose] def fullSize (k : Nat) : Nat := [1, 8292375, 98280, 8386560].getD k 0

@[expose] def fullOrb (k : Nat) : VOrbit :=
  vOrbitBFS 24 CFSG.Sporadic.Co1.Native.co1Data.colsA CFSG.Sporadic.Co1.Native.co1Data.colsB
    (fullRoot k) (fullSize k)

@[expose] def fullOKOf (k : Nat) (O : VOrbit) : Bool :=
  enumOK CFSG.Sporadic.Co1.Native.co1Data.colsA CFSG.Sporadic.Co1.Native.co1Data.colsB
      (fullRoot k) (fullSize k) O &&
    allIn 0 (fullSize k) fun i => decide (fullRoot k ≤ O.pts[i]!)

@[expose] def fullOK (k : Nat) : Bool := fullOKOf k (fullOrb k)

end Native

end CFSG.Sporadic.Co1Schreier
