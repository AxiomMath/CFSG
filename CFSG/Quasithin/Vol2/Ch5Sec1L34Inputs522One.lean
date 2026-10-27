module

public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_22_one_Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      oThreePrimeResidual (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) ≤
        (T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) ⊔ B

@[expose] def Stmt5_1_22_one_X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      ∀ x ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G), ∃ a b : ℕ, x ^ (2 ^ a * 3 ^ b) = 1

end CFSG.Quasithin.H13
