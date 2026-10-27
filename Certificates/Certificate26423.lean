module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin
import Certificates.Kernel.TwoHSLe4.TF1
import Certificates.Kernel.TwoHSLe4.USList

public section

open CFSG.EvenSporadicStandard.TwoHS

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26423 : TFacts alpha1 :=
  tfacts_of_check alpha1 KernelTwoHSLe4.omList_two KernelTwoHSLe4.TF.tfR_alpha1

end Certificates
