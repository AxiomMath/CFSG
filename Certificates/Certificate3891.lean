module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884V6

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3891 : ∃ I cents recs, l2SurvActOK 6 I cents recs = true :=
  ⟨invRows53.flatten, cents6, recs6, survAct6⟩

end Certificates
