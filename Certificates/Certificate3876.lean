
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3873C3

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3876 : t1KillRange 30 = true := by
  refine t1KillRange_of 30 fun i hi h1 h2 => ?_
  interval_cases i
  exacts [cand30, cand31, cand32, cand33, cand34, cand35, cand36, cand37, cand38, cand39]

end Certificates
