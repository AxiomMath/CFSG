module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ordG2_pow_three_eq (a : ℕ) (ha : 1 ≤ a) :
    ordG2 (a ^ 3) = ordG2 a * (a ^ 12 * (a ^ 4 + a ^ 2 + 1) * (a ^ 12 + a ^ 6 + 1)) := by
  unfold ordG2
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have h6 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ ha
  have h18 : 1 ≤ (a ^ 3) ^ 6 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ ha)
  have h6' : 1 ≤ (a ^ 3) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ ha)
  zify [h2, h6, h18, h6']
  ring

theorem three_dvd_ordG2_quotient (a : ℕ) :
    3 ∣ a ^ 12 * (a ^ 4 + a ^ 2 + 1) * (a ^ 12 + a ^ 6 + 1) := by
  have hr : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  apply Nat.dvd_of_mod_eq_zero
  rcases hr with hr | hr | hr <;> simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, hr]

theorem three_mul_ordG2_dvd (a : ℕ) : 3 * ordG2 a ∣ ordG2 (a ^ 3) := by
  by_cases ha : 1 ≤ a
  · rw [ordG2_pow_three_eq a ha, mul_comm 3 (ordG2 a)]
    exact Nat.mul_dvd_mul_left (ordG2 a) (three_dvd_ordG2_quotient a)
  · have : a = 0 := by omega
    subst this
    simp [ordG2]

section Outer


theorem card_of_chevalleyExceptionalModel_G2 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .G2 p f) : Nat.card S = ordG2 (p ^ f) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  rw [Nat.card_congr e.toEquiv, Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]

theorem outerRow_of_chevalleyExceptionalModel_G2 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .G2 p f) (hZ : Subgroup.center S = ⊥) : OuterRow S := by
  have hcard := card_of_chevalleyExceptionalModel_G2 h
  refine outerRow_of_fixed_card_dvd hZ fun σ hσ hout => ?_
  have hLie : LieModel S .G2 0 p f := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  rcases HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 S 0 p f h.1 hLie (by decide) 3
      Nat.prime_three (by norm_num) (by simp [lieOrderDivisor]) (by decide) σ hσ hout with
    ⟨f₀, hf₀, hdvd⟩ | ⟨h1, -⟩
  · refine ⟨fixedSubgroup σ, ordG2 (p ^ f₀), fun x => Iff.rfl, hdvd, ?_⟩
    rw [hcard, hf₀, mul_comm 3 f₀, pow_mul]
    exact three_mul_ordG2_dvd (p ^ f₀)
  · exact absurd h1 (by decide)

end Outer

end CFSG.RankThree.PartTwo.Sec4.RonanK432
