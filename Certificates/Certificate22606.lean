module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs
import Certificates.Kernel.Census.Small.C22606

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22606 :
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
        e₁⁻¹ * e₂ * SE.invRep 1 = SE.invRep 1 * (e₁⁻¹ * e₂)) := KernelCensus.check22606

end Certificates
