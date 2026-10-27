module

public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.SporSch.Co1.ThreeLocal

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native in
theorem certificate2150 : Native.threeLocalCheck = true := KernelSporSch.Co1ThreeLocal.check

end Certificates
