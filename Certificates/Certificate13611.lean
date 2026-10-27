module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2FiveRankInputs
import Certificates.Kernel.Co2Five.Rank

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native in
theorem certificate13611 : co2RankCheck () = true := KernelCo2Five.rank_ok

end Certificates
