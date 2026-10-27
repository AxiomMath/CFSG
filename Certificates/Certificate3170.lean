module

public import Certificates.Data.CFSGNative.McL.Certificate
import Certificates.Kernel.Sporadic.McLK.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.McL.Native in
theorem certificate3170 : mclCertificate 3 = true := KernelSpor.McLK.mcl_cert

end Certificates
