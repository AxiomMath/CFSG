module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_18_DL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_14 G T M L V H B D n → Even n →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) → D₃ ≠ B →
          ¬ D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

@[expose] def Stmt5_1_18_D5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_14 G T M L V H B D n → (n = 4 ∨ n = 8) →
      ∀ D₃ : Subgroup G, D₃ ≤ D → Nat.card D₃ = 3 →
        D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G) → D₃ ≠ B →
        ¬ D ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
          ∀ D₅ : Subgroup G, D₅ ≤ D → Nat.card D₅ = 5 →
            D₅ ≤ Subgroup.normalizer (oTwoUpper H : Set G)

end CFSG.Quasithin.H13
