module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTriD4ThreeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTriD4LineBound (p : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
      Nat.card A ≤ p ^ 3

@[expose] def GGTriD4LineWeylKnown (p : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
        ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a₀ l)) → GGFixCompCyclic p a₀ →
          (∃ n : L', (∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧
              ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
            MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀) ∨
          ∃ f ∈ A, f ∉ Subgroup.zpowers a₀ ∧
            ∀ J₁ : Subgroup L', IsComponentOf J₁ (ggFix a₀) → ∀ l ∈ J₁, f l = l

theorem ggTriD4LineKnown_iff {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)} :
    GGTriD4LineKnown p R I F ↔ GGTriD4LineBound p R I F ∧ GGTriD4LineWeylKnown p R I F := by
  constructor
  · intro h
    constructor
    · intro L' _ _ ψ hψ hker hperf A hA hAI
      exact (h L' ψ hψ hker hperf A hA hAI).1
    · intro L' _ _ ψ hψ hker hperf A hA hAI hcard hcent a₀ ha₀ ha₀' hφ hfix
      exact (h L' ψ hψ hker hperf A hA hAI).2 hcard hcent a₀ ha₀ ha₀' hφ hfix
  · rintro ⟨h1, h2⟩ L' _ _ ψ hψ hker hperf A hA hAI
    exact ⟨h1 L' ψ hψ hker hperf A hA hAI,
      fun hcard hcent a₀ ha₀ ha₀' hφ hfix =>
        h2 L' ψ hψ hker hperf A hA hAI hcard hcent a₀ ha₀ ha₀' hφ hfix⟩

@[expose] def GGNbrKGFieldTriD4ThreeLineWeyl : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .triD4 → 2 ≤ lab.n →
    3 ∣ 2 ^ lab.n - 1 →
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTriD4LineWeylKnown 3 R I F

end CFSG.StandardType

end
