
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3873C5

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3878 : t1KillRange 50 = true := by
  refine t1KillRange_of 50 fun i hi h1 h2 => ?_
  interval_cases i
  exacts [cand50, cand51, cand52, cand53, cand54, cand55, cand56, cand57, cand58, cand59]

end Certificates
