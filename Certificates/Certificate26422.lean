module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin
import Certificates.Kernel.TwoHSLe4.Cand

public section

open CFSG.EvenSporadicStandard.TwoHS

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26422 : CandFacts :=
  candFacts_of_raw (of_decide_eq_true KernelTwoHSLe4.candR_check_true)

end Certificates
