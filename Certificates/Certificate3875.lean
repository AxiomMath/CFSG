
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3873C2

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3875 : t1KillRange 20 = true := by
  refine t1KillRange_of 20 fun i hi h1 h2 => ?_
  interval_cases i
  exacts [cand20, cand21, cand22, cand23, cand24, cand25, cand26, cand27, cand28, cand29]

end Certificates
