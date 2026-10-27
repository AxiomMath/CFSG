module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884V2

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3887 : ∃ I cents recs, l2SurvActOK 2 I cents recs = true :=
  ⟨invRows20.flatten, cents2, recs2, survAct2⟩

end Certificates
