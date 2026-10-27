
module


public import Certificates.Data.CFSGNative.ON.Certificate
import Certificates.Kernel.Sporadic.ONC.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.ON.Native in
theorem certificate3171 : onCertificate 3 = true := KernelSpor.ONC.on_cert

end Certificates
