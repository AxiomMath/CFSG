module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847G4 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q →
    ∀ p ∈ D.sig,
      (F08.Thin8 Y ∨ ∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ 2 ^ (2 * n) ≡ 1 [MOD q]) →
      (normalizer (X : Set G) ≤ D.M ∨
        (∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧
          D.M ≤ normalizer (Y : Set G) ∧ p = 3 ∧ evenRank G = 3 ∧ 2 ^ n ≡ 1 [MOD q]) ∨
        (∃ ℓ f : ℕ, LieModel (Bar2 Y) .PSL 2 ℓ f ∧ p = 3 ∧
          pCoreOf 2 D.M ⊓ centralizer (X : Set G) = ⊥ ∧ evenRank G = 3 ∧
          ∃ (A : Type) (_ : Group A), LieModel A .PSL 2 ℓ f ∧
            Nonempty (↥(genFittingFStar (Bar2 D.M)) ≃*
              A × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))))

theorem r847G4_of_r847 {D : Data G} (h : F08.R847 D) : R847G4 D := by
  intro Y hY X hXY q hq hq2 hXq p hp hcase
  rcases h Y hY X hXY q hq hq2 hXq p hp hcase with h1 | ⟨n, hn, h6, hN, hp3, he, hqn⟩ |
      ⟨ℓ, f, hL, hp3, hQ, he, -, -, A, hA, hLA, hiso⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨n, hn, Or.inl (by unfold Nat.ModEq at h6; omega), hN, hp3, he, hqn⟩)
  · exact Or.inr (Or.inr ⟨ℓ, f, hL, hp3, hQ, he, A, hA, hLA, hiso⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22
