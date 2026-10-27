module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs
import Certificates.Kernel.Census.Small.C22600

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22600 : (∀ s : SE, s * s = 1 → s ≠ 1 → ∃ i : Fin 9, ∃ g : SE, g⁻¹ * s * g = SE.invRep i)
    ∧ (∀ i j : Fin 9, ∀ g : SE, g⁻¹ * SE.invRep i * g = SE.invRep j → i = j)
    ∧ (∀ s : SE, (∀ g : SE, g * s = s * g) → s = 1 ∨ s = SE.gen 0) := KernelCensus.check22600

end Certificates
