
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3873C4

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3877 : t1KillRange 40 = true := by
  refine t1KillRange_of 40 fun i hi h1 h2 => ?_
  interval_cases i
  exacts [cand40, cand41, cand42, cand43, cand44, cand45, cand46, cand47, cand48, cand49]

end Certificates
