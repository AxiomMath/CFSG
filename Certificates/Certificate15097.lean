module

public import Certificates.Data.AS81SHatClosed
import Certificates.Kernel.LocalComp.SHatClosed.Check

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15097 : CFSG.ComponentClassification.AS81.SHatClosed.f1OK = true ∧
    CFSG.ComponentClassification.AS81.SHatClosed.f2OK = true ∧
    CFSG.ComponentClassification.AS81.SHatClosed.f3OK = true :=
  KernelLC.SHatD.shat_checks

end Certificates

end
