module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

@[expose] def W3Thm88 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {V H T : Subgroup G} {i : ℕ}, Hyp88 V H T i → Concl881 V H ∧ Concl882 V H

@[expose] def W3Thm183 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G), WeakClosureSetting D V₀ V → V₀ ≠ ⊥ →
    ∀ H : Subgroup G, W3Hyp171 D H → ∀ i : ℕ, i ≤ 1 →
      normalizer (E3.wClos V i D.T : Set G) ≤ D.M → ¬ H ≤ D.M →
      (W3Hyp181 D H → MBarGT D.M V₀ V 2 → F12.HasCompFactor H IsCalL1) ∧
        (W3Hyp182 D H → MBarGT D.M V₀ V (i + 2) → F12.HasCompFactor H IsCalL0)

@[expose] def W3Thm193 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G), WeakClosureSetting D V₀ V → V₀ ≠ ⊥ →
    ∀ (p : ℕ) (X : Subgroup G), p.Prime → p ≠ 2 → IsPGroup p X → ¬ IsCyclic X →
      (∀ x ∈ X, x ^ p = 1) →
      (∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥) →
      (∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → UniqueMax D.M Y) →
      (X : Set G) * (D.T : Set G) = (D.T : Set G) * (X : Set G) → X ⊔ D.T ≤ D.M →
      Fstar (X ⊔ D.T) = pCoreOf 2 (X ⊔ D.T) →
      MBarGT D.M V₀ V 2 → rankThreeGamma 1 2 (centerOf D.T) ≤ D.M →
      normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M ∨
        normalizer (omegaOneCenterOf (E3.wClos V 1 D.T) : Set G) ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
