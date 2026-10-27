module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIPk
import Certificates.Kernel.Census.L34E16

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoL3Four.HypII in
theorem certificate15014 : l34CheckWE16 ⟨l34Prog, l34SG, l34CS⟩ = true :=
  KernelCensus.L34K.l34CheckWE16_eq_true

end Certificates

end
