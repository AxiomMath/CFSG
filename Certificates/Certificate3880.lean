module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Enum
import Certificates.Kernel.OmegaEight.SB3880C0
import Certificates.Kernel.OmegaEight.SB3880C1

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3880 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3880 : (s2BasicCheck = true)
    ∧ (∃ W, l2eSurvOK 0 W = true)
    ∧ (∃ W, l2eSurvOK 1 W = true) :=
  ⟨basic, ⟨W0, surv0⟩, ⟨W1, surv1⟩⟩

end Certificates
