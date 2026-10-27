module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Step5

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem Setting.eq_of_maximal_prime_le (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S M₁ M₂ : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hM₁ : Maximal (solvableSignalizerCompatible p 1 A θ) M₁)
    (hM₂ : Maximal (solvableSignalizerCompatible p 1 A θ) M₂) (h₁ : S ≤ M₁) (h₂ : S ≤ M₂) :
    M₁ = M₂ :=
  h.step3 hq hS hM₁ hM₂ h₁ h₂

theorem Setting.exists_not_thompsonFactorizable (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S M : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hM : Maximal (solvableSignalizerCompatible p 1 A θ) M) (hSM : S ≤ M) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ S ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      (∃ T : Subgroup G, IsSylowOf q T (signalizerNormalizerCompletion p 1 A θ Q) ∧
        A ≤ Subgroup.normalizer (T : Set G) ∧
        ¬ ThompsonFactorizable q (signalizerNormalizerCompletion p 1 A θ Q) T) ∧
      ¬ signalizerNormalizerCompletion p 1 A θ Q ⊓ signalizerCommonFixed p 1 A θ ≤ M :=
  h.step4 hq hS hM hSM

theorem Setting.exists_elemAbelian_nine_eight (h : Setting p A θ) :
    (∃ E : Subgroup G, E ≤ signalizerCommonFixed p 1 A θ ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9) ∧
    ∃ E : Subgroup G, E ≤ signalizerCommonFixed p 1 A θ ∧ IsElemAbelian 2 E ∧
      Nat.card E = 8 :=
  h.step5

end CFSG.SignalizerFunctorTheorem.Glauberman
