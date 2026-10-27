module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884V7

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3892 : ∃ I cents recs, l2SurvActOK 7 I cents recs = true :=
  ⟨invRows63.flatten, cents7, recs7, survAct7⟩

end Certificates
