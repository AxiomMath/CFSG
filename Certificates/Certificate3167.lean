module

public import Certificates.Data.CFSGNative.HS.Data
import Certificates.Kernel.VecCert.HSFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.HS in
theorem certificate3167 : vecCert Native.hsData 3 = true := KernelVec.HS.vecCert_hs

end Certificates
