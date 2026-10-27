module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Enum
import Certificates.Kernel.OmegaEight.SB3880C2
import Certificates.Kernel.OmegaEight.SB3880C3

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3880 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3881 : (∃ W, l2eSurvOK 2 W = true)
    ∧ (∃ W, l2eSurvOK 3 W = true) :=
  ⟨⟨W2, surv2⟩, ⟨W3, surv3⟩⟩

end Certificates
