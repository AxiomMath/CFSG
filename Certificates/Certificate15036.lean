module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzW
import Certificates.Kernel.Census.Suz.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Suz CFSG.KC.Census in
theorem certificate15036 : ∃ d : ConjDataP, suzCheckWII d = true := KernelCensus.Suz.suz_okII

end Certificates
