module

public import CFSG.Quasithin.Vol2.Ch10StatementsB
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Fact10_2_3Cartan : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → InM T M → Subgroup.normalizer (T : Set G) ≤ M → IsHStar T M H →
    1 < E1.nParam H →
      ∃ n : ℕ, E1.nParam H = n ∧ ∀ B : Subgroup G,
        QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ M) → ∃ b ∈ B, orderOf b = 2 ^ n - 1

@[expose] def Fact10_2_3Wreath : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H B : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → InM T M → Subgroup.normalizer (T : Set G) ≤ M → IsHStar T M H →
    E1.nParam H = 2 → QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ M) → Nat.card B = 9 →
    8 ≤ Nat.card (autOn T B) →
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo)

end CFSG.Quasithin.Vol2.Ch10.SecB
