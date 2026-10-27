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
public import CFSG.Sporadic.Schreier.Co1LiftCheckInputs
public import Certificates.Certificate2139

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

end Native

theorem lift_check : Native.liftCheck = true :=
  Certificates.certificate2139

end CFSG.Sporadic.Co1Schreier
