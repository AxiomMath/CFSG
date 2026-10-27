
module

public import CFSG.Sporadic.Co1.Module.OddNativeBase

public import CFSG.Sporadic.Co1.Module.FormsBase1
public import Certificates.Data.CFSGNative.Co1.Odd
public import Certificates.Certificate10074
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public import Certificates.Certificate10074Base

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix

attribute [local instance] vecAct vecSMul

section SLP

variable {M : Type*} [Monoid M]

end SLP

theorem orbitOK_v₂ :
    vOrbitOK 24 98280 dat.colsA dat.colsB (orbitOf 2 98280) = true :=
  Certificates.certificate10074

end CFSG.Sporadic.Co1.Module.Odd
