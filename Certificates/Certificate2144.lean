module

public import CFSG.Sporadic.Schreier.Co1QuotCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1QuotData
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
import Certificates.Kernel.SporSch.Co1.Quot

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2144 : Native.quotCheck = true := KernelSporSch.Co1Quot.check

end Certificates
