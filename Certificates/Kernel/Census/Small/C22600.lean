module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.ComponentClassification.GHarris.SCert in
theorem check22600 : (∀ s : SE, s * s = 1 → s ≠ 1 → ∃ i : Fin 9, ∃ g : SE, g⁻¹ * s * g = SE.invRep i)
    ∧ (∀ i j : Fin 9, ∀ g : SE, g⁻¹ * SE.invRep i * g = SE.invRep j → i = j)
    ∧ (∀ s : SE, (∀ g : SE, g * s = s * g) → s = 1 ∨ s = SE.gen 0) := by
  repeat' apply And.intro
  all_goals decide +kernel

end CertificateChecks.KernelCensus
