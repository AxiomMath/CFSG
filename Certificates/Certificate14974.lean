module

public import Certificates.Data.E8FiveStab
import Certificates.Kernel.E8Five.Checks
import CFSG.Certificates.Kernel.E8Five.Sound

open CFSG.KC.E8Five CertificateChecks.KernelE8Five

public section

namespace Certificates

open CFSG.RankThree.PartOne.KE8F in
theorem certificate14974 : E8FiveTorsionCount := by
  refine torsionCount_of_checks ch14974kM2 ch14974kM3 ?_ ?_
  · intro j hj
    interval_cases j
    exacts [ch14974kH20, ch14974kH21, ch14974kH22, ch14974kH23, ch14974kH24]
  · intro j hj
    interval_cases j
    exacts [ch14974kH30, ch14974kH31, ch14974kH32, ch14974kH33, ch14974kH34]

end Certificates
