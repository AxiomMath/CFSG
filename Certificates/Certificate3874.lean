
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3873C1

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3874 : t1KillRange 10 = true := by
  refine t1KillRange_of 10 fun i hi h1 h2 => ?_
  interval_cases i
  exacts [cand10, cand11, cand12, cand13, cand14, cand15, cand16, cand17, cand18, cand19]

end Certificates
