module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Enum
import Certificates.Kernel.OmegaEight.SB3880C4
import Certificates.Kernel.OmegaEight.SB3880C5

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3880 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3882 : (∃ W, l2eSurvOK 4 W = true)
    ∧ (∃ W, l2eSurvOK 5 W = true) :=
  ⟨⟨W4, surv4⟩, ⟨W5, surv5⟩⟩

end Certificates
