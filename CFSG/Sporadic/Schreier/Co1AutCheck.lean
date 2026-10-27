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
public import CFSG.Sporadic.Schreier.Co1AutCheckInputs
public import Certificates.Certificate2130

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

end Native

theorem stab_tower_check : Native.stabTowerCheck = true :=
  Certificates.certificate2130.1

theorem nonlin_check : Native.nonlinCheck = true :=
  Certificates.certificate2130.2

end CFSG.Sporadic.Co1Schreier
