
module

public import Certificates.Certificate3024Base

public import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.VecCert.Co1Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1 in
theorem certificate3024 : vecCert Native.co1Data 3 = true := KernelVec.Co1.vecCert_co1

end Certificates
