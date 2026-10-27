module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884V1

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3886 : ∃ I cents recs, l2SurvActOK 1 I cents recs = true :=
  ⟨invRows10.flatten, cents1, recs1, survAct1⟩

end Certificates
