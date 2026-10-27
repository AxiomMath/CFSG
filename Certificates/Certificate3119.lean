module

public import Certificates.Data.CFSGNative.J1.Certificate
import Certificates.Kernel.Sporadic.J1K.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J1.Native in
theorem certificate3119 : j1Certificate 3 = true := KernelSpor.J1K.j1_cert

end Certificates
