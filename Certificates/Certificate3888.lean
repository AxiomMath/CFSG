module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884V3

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3888 : ∃ I cents recs, l2SurvActOK 3 I cents recs = true :=
  ⟨invRows30.flatten, cents3, recs3, survAct3⟩

end Certificates
