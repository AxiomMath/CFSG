module

public import Certificates.Data.CFSGNative.Co3.Data
import Certificates.Kernel.VecCert.Co3Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co3 in
theorem certificate3091 : vecCert Native.co3Data 3 = true := KernelVec.Co3.vecCert_co3

end Certificates
