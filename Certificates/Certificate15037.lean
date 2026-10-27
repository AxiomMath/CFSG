module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzW
import Certificates.Kernel.Census.Suz.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Suz CFSG.KC.Census in
theorem certificate15037 : ∃ d : ConjDataP, suzCheckWExc suzE0 d = true := KernelCensus.Suz.suz_okExc

end Certificates
