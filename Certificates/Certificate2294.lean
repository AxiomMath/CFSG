module

public import CFSG.Sporadic.SuzOddCore.GammaStab
import Certificates.Kernel.Sporadic.OddCore.SuzGamFacts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore in
theorem certificate2294 :     (∀ i : Fin 22880, suzGamma.Adj 0 i ↔ i ∈ suzDeltaΩ) ∧
    (∀ s < 4, (MulAction.orbit (gammaStab s) (gammaBasePt s)).ncard ≤ gammaBounds s) ∧
    gammaStab 4 = ⊥ := KernelSpor.OddCore.SGam.gammaFacts

end Certificates
