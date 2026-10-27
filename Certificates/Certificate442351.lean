module

public import Certificates.Data.FzFusK3
import CFSG.Certificates.Kernel.FzFus.Complete
import Certificates.Kernel.FzFus.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate442351 : Certificates.FzFus.fusCheck () = true :=
  CFSG.KC.FzFus.fusCheck_of KernelFzFus.classFact KernelFzFus.rowsFact KernelFzFus.subsFact
    KernelFzFus.pair7Fact

end Certificates
