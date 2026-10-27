module

public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Ch5L2ChoiceExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D →
      ∃ L₂ : Subgroup G, IsL2Choice T H L₂

@[expose] def RankTwoParabolicFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (k : ℕ), 2 ≤ k →
    (IsSL3Ch5 k X ∨ LieModel X .PSp 2 2 k) →
    ∀ S P : Subgroup X, IsSylowTwoOf S ⊤ → Subgroup.normalizer (S : Set X) ≤ P → P ≠ ⊤ →
      (∀ Q : Subgroup X, P ≤ Q → Q ≠ ⊤ → Q = P) → ¬ Group.IsSolvable ↥P

end CFSG.Quasithin.H13
