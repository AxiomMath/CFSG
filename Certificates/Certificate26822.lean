module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUFacts
import Certificates.Kernel.TwoHSLe4.USList
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin

public section

open CFSG.EvenSporadicStandard.TwoHS

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26822 : UFactsOf (sList alpha2) :=
  ufactsOf_of_check alpha2 KernelTwoHSLe4.omList_two KernelTwoHSLe4.uSCheck_alpha2

end Certificates
