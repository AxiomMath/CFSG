module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Enum
import Certificates.Kernel.OmegaEight.SB3880C6
import Certificates.Kernel.OmegaEight.SB3880C7

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3880 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3883 : (∃ W, l2eSurvOK 6 W = true)
    ∧ (∃ W, l2eSurvOK 7 W = true) :=
  ⟨⟨W6, surv6⟩, ⟨W7, surv7⟩⟩

end Certificates
