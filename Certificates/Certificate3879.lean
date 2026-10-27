
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3873C6

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3879 : t1KillRange 60 = true := by
  refine t1KillRange_of 60 fun i hi h1 h2 => ?_
  interval_cases i
  exacts [cand60, cand61, cand62, cand63]

end Certificates
