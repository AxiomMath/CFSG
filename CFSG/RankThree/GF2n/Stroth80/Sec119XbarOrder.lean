module

public import CFSG.Blueprint.Catalog
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ClassicalOrders

private theorem orderFactor_nonneg {r : ℤ} (hr : 1 ≤ r) (m : ℕ) :
    0 ≤ r ^ (m * (m - 1)) * ∏ i ∈ Finset.Icc 1 (m - 1), (r ^ (2 * i) - 1) := by
  refine mul_nonneg (pow_nonneg (by omega) _) (Finset.prod_nonneg fun i _ => ?_)
  have : 1 ≤ r ^ (2 * i) := one_le_pow₀ hr
  linarith

private theorem card_eq_of_lieModel_omegaPlus {Y : Type} [Group Y] {m x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .POmegaPlus m 2 x) :
    (Nat.card Y : ℤ) = ((2 : ℤ) ^ x) ^ (m * (m - 1)) * (((2 : ℤ) ^ x) ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), (((2 : ℤ) ^ x) ^ (2 * i) - 1) := by
  obtain ⟨⟨-, -, hm⟩, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have := charP_two_of_card_eq hK
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedOmega_quadPlus hm, hK]
  push_cast
  rfl

private theorem card_eq_of_lieModel_omegaMinus {Y : Type} [Group Y] {m x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .POmegaMinus m 2 x) :
    (Nat.card Y : ℤ) = ((2 : ℤ) ^ x) ^ (m * (m - 1)) * (((2 : ℤ) ^ x) ^ m + 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), (((2 : ℤ) ^ x) ^ (2 * i) - 1) := by
  obtain ⟨⟨-, -, hm⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have := charP_two_of_card_eq hK
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedOmega_quadMinus hm hirr, hK]
  push_cast
  rfl

private theorem cast_toNat_pow_sub_neg_one_pow {r i : ℕ} (hr : 1 ≤ r) :
    ((((r : ℤ) ^ i - (-1 : ℤ) ^ i).toNat : ℕ) : ℤ) = (r : ℤ) ^ i - (-1 : ℤ) ^ i := by
  refine Int.toNat_of_nonneg ?_
  have h1 : (1 : ℤ) ≤ (r : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hr)
  rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> linarith

private theorem card_eq_of_lieModel_psu4 {Y : Type} [Group Y] {x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSU 4 2 x) :
    (Nat.card Y : ℤ) = ((2 : ℤ) ^ x) ^ 6 *
      ((((2 : ℤ) ^ x) ^ 2 - 1) * ((((2 : ℤ) ^ x) ^ 3 + 1) * (((2 : ℤ) ^ x) ^ 4 - 1))) := by
  have hx : 1 ≤ x := h.admissible.2.1
  have hg : Nat.gcd (3 + 1) (2 ^ x + 1) = 1 := by
    simpa using gcd_four_eq_one (odd_two_pow_pow_add_one hx (n := 1) le_rfl)
  have hr : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  rw [(card_statedClassicalModel_two (h.statedClassicalModel (by decide))).2.1 rfl,
    show (4 - 1 : ℕ) = 3 from rfl, ordTwistedA, hg, Nat.div_one,
    show 3 * (3 + 1) / 2 = 6 from rfl, show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl,
    Finset.prod_insert (by decide), Finset.prod_pair (by norm_num), Nat.cast_mul, Nat.cast_mul,
    Nat.cast_mul, cast_toNat_pow_sub_neg_one_pow hr, cast_toNat_pow_sub_neg_one_pow hr,
    cast_toNat_pow_sub_neg_one_pow hr]
  push_cast
  ring

theorem card_ge_of_omega_lieModel {Y : Type} [Group Y] {m x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel Y .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel Y .PSU 4 2 x)) :
    ((2 : ℤ) ^ x) ^ (m * (m - 1)) * (((2 : ℤ) ^ x) ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), (((2 : ℤ) ^ x) ^ (2 * i) - 1) ≤ Nat.card Y := by
  have hr : (1 : ℤ) ≤ 2 ^ x := one_le_pow₀ (by norm_num)
  rcases h with h | h | ⟨rfl, h⟩
  · exact (card_eq_of_lieModel_omegaPlus h).ge
  · rw [card_eq_of_lieModel_omegaMinus h]
    have hA := orderFactor_nonneg hr m
    nlinarith
  · rw [card_eq_of_lieModel_psu4 h, show Finset.Icc 1 (3 - 1) = {1, 2} from rfl,
      Finset.prod_pair (by norm_num)]
    have h6 : (0 : ℤ) ≤ ((2 : ℤ) ^ x) ^ 6 := by positivity
    have h2 : (0 : ℤ) ≤ ((2 : ℤ) ^ x) ^ 2 - 1 := by nlinarith [one_le_pow₀ (n := 2) hr]
    have h4 : (0 : ℤ) ≤ ((2 : ℤ) ^ x) ^ 4 - 1 := by nlinarith [one_le_pow₀ (n := 4) hr]
    have h24 := mul_nonneg (mul_nonneg h6 h2) h4
    norm_num
    nlinarith

end CFSG.RankThree.GF2n.Stroth80
