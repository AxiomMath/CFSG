
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3873C0

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3873 : t1KillRange 0 = true := by
  refine t1KillRange_of 0 fun i hi h1 h2 => ?_
  interval_cases i
  exacts [cand0, cand1, cand2, cand3, cand4, cand5, cand6, cand7, cand8, cand9]

end Certificates
