
module


public import Certificates.Data.CFSGNative.Suz.Certificate
import Certificates.Kernel.Sporadic.SuzK.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Suz.Native in
theorem certificate3173 : suzCertificate 3 = true := KernelSpor.SuzK.suz_cert

end Certificates
