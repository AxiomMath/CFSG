module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs517Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def A126TwoFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X V : Subgroup G), X ≤ H → oTwoUpper X = X →
    V ≤ H → IsPGroup 2 V → ⁅V, X⁆ = V → Group.IsSolvable ↥H →
    (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2) →
    Subgroup.closure {x | x ∈ X ∧ Nat.Coprime (orderOf x) 6} = X →
      V ≤ pCoreOf 2 H

@[expose] def Stmt5_1_17_noBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Setup5_1_17Odd G T M L V H B D n → ¬ ⁅pCoreOf 2 L, L⁆ ≤ V

end CFSG.Quasithin.H13
