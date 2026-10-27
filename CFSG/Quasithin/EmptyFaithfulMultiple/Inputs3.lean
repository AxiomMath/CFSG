module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def InputE213Solvable : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ),
    MinParabolic H T M → Group.IsSolvable H →
    (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2) → CharTwo H →
    V ≤ T → T ≤ Subgroup.normalizer (V : Set Γ) → IsElemAbelian 2 V →
    V ≤ pCoreOf 2 M → ¬ V ≤ kerIn M H →
    ∃ A : Subgroup Γ, A ≤ T ∧ IsElemAbelian 2 A ∧
      ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧ ¬ A ≤ Subgroup.centralizer (V : Set Γ) ∧
      (V ⊓ Subgroup.centralizer (A : Set Γ)).relIndex V ≤
        ((A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A) ^ 2

end CFSG.Quasithin.EmptyFaithfulMultiple
