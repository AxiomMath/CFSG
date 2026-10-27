module

public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Open (ordTwistedA)
open CFSG.RankThree.PartTwo.Sec21

theorem ordTwistedA_four_eq {b : ℕ} :
    ordTwistedA 4 (2 ^ b) =
      ((2 ^ b) ^ 10 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * ((2 ^ b) ^ 4 - 1) *
        ((2 ^ b) ^ 5 + 1))) / Nat.gcd 5 (2 ^ b + 1) := by
  have hq : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rw [ordTwistedA, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} by rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd (by decide),
    show 4 * (4 + 1) / 2 = 10 by rfl]
  congr 1
  ring

theorem odd_ordTwistedA_four_part {b : ℕ} (hb : 1 ≤ b) :
    Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * ((2 ^ b) ^ 4 - 1) * ((2 ^ b) ^ 5 + 1)) :=
  (((CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos).mul
    (CFSG.Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num))).mul
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))).mul
    (CFSG.Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num))

theorem padicValNat_ordTwistedA_four {b : ℕ} (hb : 1 ≤ b) :
    padicValNat 2 (ordTwistedA 4 (2 ^ b)) = 10 * b := by
  rw [ordTwistedA_four_eq]
  set X := (2 ^ b) ^ 10 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * ((2 ^ b) ^ 4 - 1) *
    ((2 ^ b) ^ 5 + 1)) with hX
  set g := Nat.gcd 5 (2 ^ b + 1) with hg
  have hgodd : Odd g := Odd.of_dvd_nat (by decide : Odd 5) (Nat.gcd_dvd_left _ _)
  have hg1 : g ∣ (2 ^ b) ^ 5 + 1 := by
    have h1 : 2 ^ b + 1 ∣ (2 ^ b) ^ 5 + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow (2 ^ b) 1 (by decide : Odd 5)
      simpa using this
    exact (Nat.gcd_dvd_right _ _).trans h1
  have hgX : g ∣ X := by
    rw [hX]
    exact Dvd.dvd.mul_left (dvd_mul_of_dvd_right hg1 _) _
  have hXval : padicValNat 2 X = b * 10 :=
    padicValNat_pow_two_pow_mul_odd (odd_ordTwistedA_four_part hb)
  have hXpos : X ≠ 0 := by
    intro h0
    rw [h0] at hXval
    simp at hXval
    omega
  have hsplit : g * (X / g) = X := Nat.mul_div_cancel' hgX
  have hq0 : X / g ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsplit
    exact hXpos hsplit.symm
  have := padicValNat.mul (p := 2) (a := g) (b := X / g) hgodd.pos.ne' hq0
  rw [hsplit, hXval, padicValNat.eq_zero_of_not_dvd hgodd.not_two_dvd_nat, zero_add] at this
  omega

theorem card_projSU_five {b : ℕ} (hb : 1 ≤ b) :
    Nat.card (projSU 5 2 b) = ordTwistedA 4 (2 ^ b) :=
  card_projSU (m := 5) (by norm_num) hb

theorem eq_of_mulEquiv_projSU_five {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (e : projSU 5 2 a ≃* projSU 5 2 b) : a = b := by
  have h := Nat.card_congr e.toEquiv
  rw [card_projSU_five ha, card_projSU_five hb] at h
  have := congrArg (padicValNat 2) h
  rw [padicValNat_ordTwistedA_four ha, padicValNat_ordTwistedA_four hb] at this
  omega

end CFSG.RankThree.PartOne.U5K.Pkg
