module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin
import Certificates.Kernel.TwoHSLe4.TF2
import Certificates.Kernel.TwoHSLe4.USList

public section

open CFSG.EvenSporadicStandard.TwoHS

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26424 : TFacts alpha2 :=
  tfacts_of_check alpha2 KernelTwoHSLe4.omList_two KernelTwoHSLe4.TF.tfR_alpha2

end Certificates
