module

public import CFSG.Quasithin.Vol2.Ch11SecSZK5
public import CFSG.Quasithin.Vol2.Ch11SecA02Five

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

namespace TypeData

variable {Y : Type} [Group Y]

theorem two_part (hD : TypeData Y) {a o : ℕ} (ho : Odd o) (h : Nat.card Y = 2 ^ a * o) :
    (a = 6 ∧ o = 315) ∨ (a = 7 ∧ o = 79695) := by
  rcases hD.card with hc | hc
  · have h1 := eq_of_two_pow_mul_odd (a := 6) (b := a) (by decide) ho (hc.symm.trans h)
    subst h1
    exact Or.inl ⟨rfl, (Nat.eq_of_mul_eq_mul_left (by positivity) (hc.symm.trans h)).symm⟩
  · have h1 := eq_of_two_pow_mul_odd (a := 7) (b := a) (by decide) ho (hc.symm.trans h)
    subst h1
    exact Or.inr ⟨rfl, (Nat.eq_of_mul_eq_mul_left (by positivity) (hc.symm.trans h)).symm⟩

theorem le_card (hD : TypeData Y) : 2 ^ 6 * 315 ≤ Nat.card Y := by
  rcases hD.card with h | h
  · rw [h]
  · rw [h]
    norm_num

theorem false_of_iso_lt (hD : TypeData Y) {Z : Type} [Group Z] (e : Y ≃* Z)
    (h : Nat.card Z < 2 ^ 6 * 315) : False := by
  have := hD.le_card
  rw [Nat.card_congr e.toEquiv] at this
  omega

theorem not_SL3 (hD : TypeData Y) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (e : Y ≃* Matrix.SpecialLinearGroup (Fin 3) K) : False := by
  have hn := one_le_of_card_eq hK
  have hc := (Nat.card_congr e.toEquiv).trans (card_SL_three' hK)
  rcases hD.two_part (odd_oSL3 hn) hc with ⟨h6, ho⟩ | ⟨h7, -⟩
  · obtain rfl : n = 2 := by omega
    exact absurd ho (by decide)
  · omega

theorem not_Sp4 (hD : TypeData Y) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (e : Y ≃* ↥(StatedSp 2 K)) : False := by
  have hn := one_le_of_card_eq hK
  have hc := (Nat.card_congr e.toEquiv).trans (card_Sp_four hK)
  rcases hD.two_part (odd_oSp4 hn) hc with ⟨h6, -⟩ | ⟨h7, -⟩ <;> omega

theorem not_SL5 (hD : TypeData Y) (e : Y ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    False := by
  have hc := (Nat.card_congr e.toEquiv).trans card_SL_five_two
  rcases hD.two_part (by decide) hc with ⟨h6, -⟩ | ⟨h7, -⟩ <;> omega

theorem not_PSL2 (hD : TypeData Y) {n : ℕ} (hL : LieModel Y .PSL 2 2 n) : False := by
  rcases hL with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨hn, hcard⟩ := card_of_isPSL_two_two hc
    rcases hD.two_part (odd_oSL2 hn) hcard with ⟨rfl, ho⟩ | ⟨rfl, ho⟩
    · exact absurd ho (by decide)
    · exact absurd ho (by decide)
  all_goals exact absurd h (by norm_num)

theorem not_G2 (hD : TypeData Y) (hF : Facts02) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (e : Y ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) : False := by
  have hn := one_le_of_card_eq hK
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    refine hD.false_of_iso_lt e ?_
    rw [hF.g2DerivedTwo K (by rw [hK]; norm_num)]
    norm_num
  · have hc := (Nat.card_congr e.toEquiv).trans (hF.g2Derived K n hn2 hK)
    rw [← pow_mul] at hc
    have ho : Odd ((2 ^ (n * 6) - 1) * ((2 ^ n) ^ 2 - 1)) := by
      refine (odd_two_pow_sub_one (by omega)).mul ?_
      rw [← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    rcases hD.two_part ho hc with ⟨h6, -⟩ | ⟨h7, -⟩ <;> omega

theorem not_tripleA6 (hD : TypeData Y) (hc : Nat.card (Subgroup.center Y) = 3) : False := by
  have := hD.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · rw [h, Subgroup.card_bot] at hc
    omega
  · rw [h, Subgroup.card_top] at hc
    have := hD.le_card
    omega

end TypeData

end CFSG.Quasithin.Vol2.Ch11.SecS
