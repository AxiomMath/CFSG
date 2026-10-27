module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSAutData
import Certificates.Kernel.OmegaEight.SB3871C2
import Certificates.Kernel.OmegaEight.SB3871C3
import Certificates.Kernel.OmegaEight.SB3871C4

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3871 : (sAutCheck1 = true)
    ∧ (sAutCheck2 = true)
    ∧ (sAutCheck3 = true)
    ∧ (sAutCheck4 = true) :=
  ⟨KernelO8.SB3871.check1, KernelO8.SB3871.check2, KernelO8.SB3871.check3,
    KernelO8.SB3871.check4⟩

end Certificates
