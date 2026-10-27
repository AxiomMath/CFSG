module

public import Certificates.Data.CFSGNative.Co2.Data
import Certificates.Kernel.VecCert.Co2Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2 in
theorem certificate3138 : vecCert Native.co2Data 3 = true := KernelVec.Co2.vecCert_co2

end Certificates
