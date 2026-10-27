module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzArith
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

theorem szOrder3Aut_holds : SzOrder3Aut := by
  intro S _ _ f hS σ hσ
  obtain ⟨b, hf, hcard, hfix⟩ := SzFix.card_fixed_of_orderOf_three hS hσ
  obtain ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, hne, h12, h22, hℓ⟩ := SzArith.exists_two_odd_primes b
  have h2f : 2 ^ f = (2 ^ (2 * b + 1)) ^ 3 := by
    rw [hf, mul_comm, pow_mul]
  have key : ∀ ℓ : ℕ, ℓ.Prime → (ℓ = ℓ₁ ∨ ℓ = ℓ₂) →
      ∀ P : Subgroup S, CFSG.ABGLocalTools.IsSylowOf ℓ P ⊤ → ∃ x ∈ P, σ x ≠ x :=
    fun ℓ hℓp hℓm P hP => by
      obtain ⟨hdvd, hnd⟩ := hℓ ℓ hℓm
      refine SzFix.exists_mem_ne_of_isSylowOf σ hℓp ?_ ?_ hP
      · rw [hcard, h2f]
        exact hdvd
      · rw [hfix]
        exact hnd
  refine ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, hne, h12, h22, fun P hP => ?_⟩
  rcases hP with hP | hP
  · exact key ℓ₁ hℓ₁ (Or.inl rfl) P hP
  · exact key ℓ₂ hℓ₂ (Or.inr rfl) P hP

end CFSG.LocalAnalysis.UniquenessCase.UCK
