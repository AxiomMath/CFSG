module

public import Certificates.Data.FzJtCheck
import CFSG.Certificates.Kernel.FzJt.Complete
import Certificates.Kernel.FzJt.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate441783 : Certificates.FzJt.fzJtCheck () = true :=
  CFSG.KC.FzJt.fzJtCheck_of KernelFzJt.f2Fact KernelFzJt.f3Fact KernelFzJt.f4Fact

end Certificates
