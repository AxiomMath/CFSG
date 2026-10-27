module

public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Timmesfeld CFSG.Timmesfeld.Orders

variable {X : Type} [Group X]

theorem rankTwo_cases
    (h : IsRankTwoLie2Derived X) :
    (IsPSL 3 2 1 X ∧ Nat.card X = 168) ∨ RankTwoOrder (Nat.card X) := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | hA | ⟨e, he⟩ | he | ⟨e, he⟩ | ⟨e, he⟩ |
    he
  · have hc : Nat.card X = ordA 2 (2 ^ e) := (card_statedClassicalModel_two he).1 rfl
    have he1 : 1 ≤ e := he.1.2.1
    rcases Nat.lt_or_ge e 2 with h1 | h2
    · obtain rfl : e = 1 := by omega
      exact Or.inl ⟨he, by rw [hc]; decide +kernel⟩
    · exact Or.inr (Or.inl ⟨e, h2, hc⟩)
  · right; right; left
    exact ⟨e, he.1.2.1, (card_statedClassicalModel_two he).2.1 rfl⟩
  · right; right; right; left
    exact ⟨e, he.1.2.1, (card_statedClassicalModel_two he).2.1 rfl⟩
  · right; right; right; right; left
    exact ⟨e, he.1.2.1, (card_statedClassicalModel_two he).2.2.1 rfl⟩
  · obtain ⟨φ⟩ := hA
    right; right; right; right; right; left
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_fin 6 (by norm_num)]
    decide
  · right; right; right; right; right; right; left
    refine ⟨e, ?_, card_chevalleyExceptionalModel_two he⟩
    obtain ⟨⟨-, he1, -, h3⟩, -⟩ := he
    by_contra hc
    obtain rfl : e = 1 := by omega
    norm_num at h3
  · right; right; right; right; right; right; right; left
    exact card_of_statedClassicalModel_psu_three_three he
  · right; right; right; right; right; right; right; right; left
    exact ⟨e, he.1.2.1, card_chevalleyExceptionalModel_two he⟩
  · right; right; right; right; right; right; right; right; right; left
    exact card_eq_ordTwistedF4_of_reeTitsModel he
  · right; right; right; right; right; right; right; right; right; right
    obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 he
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD, ordTits_eq]
    norm_num

theorem rankTwoA38Types_holds
    : ∀ (X : Type) [Group X] [Finite X], A38Types X →
    IsRankTwoLie2Derived (X ⧸ Subgroup.center X) → IsPSL 3 2 1 X := by
  intro X _ _ hA hR
  have hS := isSimpleGroup_of_a38Types hA
  have hcases := rankTwo_cases hR
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
      have hcZ : Nat.card (Subgroup.center X) = Nat.card X := by rw [h, Subgroup.card_top]
      rw [hcZ] at hc
      have h1 : Nat.card (X ⧸ Subgroup.center X) = 1 :=
        Nat.eq_of_mul_eq_mul_right Nat.card_pos (hc.symm.trans (one_mul _).symm)
      rcases hcases with ⟨-, h168⟩ | hb
      · omega
      · exact rankTwoOrder_ne_one hb h1
  let φ : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rcases hcases with ⟨hL, -⟩ | hb
  · exact isPSL_of_mulEquiv hL φ
  · rw [Nat.card_congr φ.toEquiv] at hb
    exact (a38Order_not_rankTwoOrder (a38Order_card hA) hb).elim

end CFSG.Quasithin.H13.VolI
