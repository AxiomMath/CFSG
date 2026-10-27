module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUFacts
import Certificates.Kernel.TwoHSLe4.USList
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin

public section

open CFSG.EvenSporadicStandard.TwoHS

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26821 : UFactsOf (sList alpha1) :=
  ufactsOf_of_check alpha1 KernelTwoHSLe4.omList_two KernelTwoHSLe4.uSCheck_alpha1

end Certificates
