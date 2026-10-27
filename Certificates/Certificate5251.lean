module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.Ivk8KBStarV.Final

public section

namespace Certificates

open CFSG.ComponentClassification.PSL3Four in
theorem certificate5251 :
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₁ * x = x * r₁ →
      ∃ c ∈ C₁, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → CFSG.ComponentClassification.PSL3Four.r₂ * x = x * CFSG.ComponentClassification.PSL3Four.r₂ →
      ∃ c ∈ C₂, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₃ * x = x * r₃ →
      ∃ c ∈ C₃, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₄ * x = x * r₄ →
      (p = 3 ∧ x ∈ CFSG.ComponentClassification.PSL3Four.S) ∨ ∃ c ∈ C₄, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ e ∈ C₄, orderOf e = 3 → ∃ c ∈ C₄, c * e * c⁻¹ ≠ e ∧ c * e * c⁻¹ * e ≠ 1) :=
  CFSG.KS.Ivk8KBStarV.Final.star_facts

end Certificates
