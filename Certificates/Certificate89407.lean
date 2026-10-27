module

public import CFSG.Quasithin.H13.AS91Sec4SevenInputs
import Certificates.Kernel.AS91K468.Checks47
import CFSG.Certificates.Kernel.AS91K468.Sound47

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.AS91 in
theorem certificate89407 : Two.ok47 () = true :=
  Certificates.Kernel.AS91K468.ok47_of KernelAS91K468.ch89407_base KernelAS91K468.ch89407_f
    KernelAS91K468.ch89407_g

end Certificates
