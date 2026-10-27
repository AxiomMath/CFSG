module

public import Certificates.Data.CFSGNative.He.Certificate
import Certificates.Kernel.Sporadic.HeK.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.He.Native in
theorem certificate3168 : heCertificate 3 = true := KernelSpor.HeK.he_cert

end Certificates
