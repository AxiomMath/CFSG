module

public import Certificates.Data.HuppertU38Q.NoE81
import Certificates.Kernel.U38Q.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate211003 : U38Sylow.u38NoE81Check () = true :=
  by rw [U38Sylow.u38NoE81Check, KernelU38Q.sylow_true, KernelU38Q.noE81_true]; rfl

end Certificates
