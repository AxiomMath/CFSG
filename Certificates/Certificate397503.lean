module

public import Certificates.Data.U43TwinCheck
import Certificates.Kernel.U43Twin.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate397503 : Certificates.U43Twin.allOK () = true := KernelU43Twin.allOK_true

end Certificates
