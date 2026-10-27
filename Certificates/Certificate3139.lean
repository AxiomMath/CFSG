module

public import Certificates.Data.CFSGNative.J2.Certificate
import Certificates.Kernel.Sporadic.J2K.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J2.Native in
theorem certificate3139 : j2Certificate 3 = true := KernelSpor.J2K.j2_cert

end Certificates
