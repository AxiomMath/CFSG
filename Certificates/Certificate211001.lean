module

public import Certificates.Data.HuppertU38Q.Check
import Certificates.Kernel.U38Q.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate211001 : U38Sylow.u38SylowCheck () = true := KernelU38Q.sylow_true

end Certificates
