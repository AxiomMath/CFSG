module

public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.Quasithin.EmptyFaithful.S151S2
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.Quasithin.H13.VolI

theorem rankTwoNotA38Type_holds :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), ListB15120' L →
      ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := by
  intro G _ _ L hB hA
  have hS := isSimpleGroup_of_a38Types hA
  have hA38 := a38Order_card hA
  rcases hB with (⟨n, hn, hY⟩ | ⟨n, hn, hY⟩ | ⟨n, hn, hY⟩) | ⟨n, hn, hY⟩
  · exact a38Order_not_rankTwoOrder hA38
      (Or.inl ⟨n, hn, (card_statedClassicalModel_two hY).1 rfl⟩)
  · exact a38Order_not_rankTwoOrder hA38
      (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, hY.1.2.1, (card_statedClassicalModel_two hY).2.2.1 rfl⟩))))
  · exact a38Order_not_rankTwoOrder hA38
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, hn, card_chevalleyExceptionalModel_two hY⟩))))))
  · have hcard : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) =
        ordA 2 (2 ^ n) := (card_statedClassicalModel_two hY).1 rfl
    have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with h | h
      · exact h
      · exfalso
        have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
        have hcZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) =
            Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by rw [h, Subgroup.card_top]
        rw [hcZ] at hc
        have h1 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) =
            1 := Nat.eq_of_mul_eq_mul_right Nat.card_pos (hc.symm.trans (one_mul _).symm)
        exact rankTwoOrder_ne_one (Or.inl ⟨n, hn, hcard⟩) (hcard ▸ h1)
    let φ : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
        (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact a38Order_not_rankTwoOrder hA38
      (Or.inl ⟨n, hn, by rw [← Nat.card_congr φ.toEquiv]; exact hcard⟩)

end CFSG.Quasithin.Rk2
