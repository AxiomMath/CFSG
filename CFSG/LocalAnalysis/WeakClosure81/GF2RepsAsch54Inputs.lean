module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

@[expose] def Asch80ThmA54 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T M : Subgroup Q), CFSG.Open.IsKGroup Q → L.Normal →
    IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) →
    Subgroup.centralizer (L : Set Q) = ⊥ → ¬ IsCalL0 ↥L → IsSylowIn 2 T ⊤ →
    M < ⊤ → (∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) →
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
        1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T)) ∨
      (¬ HasCompFactor M IsCalL0 ∧ Shape54 ⊤ T L)

@[expose] def Asch54ONGen : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q), L.Normal →
    Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.ON) →
    Subgroup.centralizer (L : Set Q) = ⊥ → IsSylowIn 2 T ⊤ → lGen IsCalL0 ⊤ T = ⊤

end CFSG.LocalAnalysis.WeakClosure81

end
