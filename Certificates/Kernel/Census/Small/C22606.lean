module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.ComponentClassification.GHarris.SCert in
theorem check22606 :
    (∀ e₁ e₂ : SE, SE.predE e₁ → SE.predE e₂ → e₁ * SE.invRep 1 = SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 = SE.invRep 1 * e₂ → ¬ SE.predF e₁ → ¬ SE.predF e₂ →
        SE.predF (e₁⁻¹ * e₂)) ∧
    (∀ e₁ e₂ : SE, SE.predE e₁ → SE.predE e₂ → e₁ * SE.invRep 1 ≠ SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 ≠ SE.invRep 1 * e₂ →
        e₁⁻¹ * e₂ * SE.invRep 1 = SE.invRep 1 * (e₁⁻¹ * e₂)) ∧
    (∀ e₁ e₂ : SE, SE.predF e₁ → SE.predF e₂ → e₁ * SE.invRep 1 = SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 = SE.invRep 1 * e₂ → ¬ SE.predE e₁ → ¬ SE.predE e₂ →
        SE.predE (e₁⁻¹ * e₂)) ∧
    (∀ e₁ e₂ : SE, SE.predF e₁ → SE.predF e₂ → e₁ * SE.invRep 1 ≠ SE.invRep 1 * e₁ →
      e₂ * SE.invRep 1 ≠ SE.invRep 1 * e₂ →
        e₁⁻¹ * e₂ * SE.invRep 1 = SE.invRep 1 * (e₁⁻¹ * e₂)) := by
  repeat' apply And.intro
  all_goals decide +kernel

end CertificateChecks.KernelCensus
