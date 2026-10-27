module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem even_two_pow_of_one_le {m : ℕ} (hm : 1 ≤ m) : Even (2 ^ m : ℕ) :=
  Nat.even_pow.mpr ⟨even_two, by omega⟩

theorem even_two_pow_pow_of_one_le {m k : ℕ} (hm : 1 ≤ m) (hk : k ≠ 0) :
    Even ((2 ^ m) ^ k) :=
  Nat.even_pow.mpr ⟨even_two_pow_of_one_le hm, hk⟩

theorem odd_two_pow_pow_sub_one {m k : ℕ} (hm : 1 ≤ m) (hk : k ≠ 0) :
    Odd ((2 ^ m) ^ k - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
    (even_two_pow_pow_of_one_le hm hk) odd_one

theorem odd_two_pow_pow_add_one {m k : ℕ} (hm : 1 ≤ m) (hk : k ≠ 0) :
    Odd ((2 ^ m) ^ k + 1) :=
  (even_two_pow_pow_of_one_le hm hk).add_one

theorem odd_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (even_two_pow_of_one_le hm) odd_one

theorem sub_one_mul_sub_one_le_pow (x a b : ℕ) : (x ^ a - 1) * (x ^ b - 1) ≤ x ^ (a + b) := by
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem add_one_le_pow_succ_of_two_le {x k : ℕ} (hx : 2 ≤ x) : x ^ k + 1 ≤ x ^ (k + 1) := by
  have h1 : 1 ≤ x ^ k := Nat.one_le_pow _ _ (by omega)
  calc x ^ k + 1 ≤ x ^ k + x ^ k := by omega
    _ = x ^ k * 2 := by ring
    _ ≤ x ^ k * x := Nat.mul_le_mul_left _ hx
    _ = x ^ (k + 1) := (pow_succ x k).symm

theorem pow_eighteen_le_sub_mul {x : ℕ} (hx : 2 ≤ x) :
    x ^ 18 ≤ (x ^ 8 - 1) * (x ^ 12 - 1) := by
  have h7 : x ^ 7 + 1 ≤ x ^ 8 := add_one_le_pow_succ_of_two_le (k := 7) hx
  have h11 : x ^ 11 + 1 ≤ x ^ 12 := add_one_le_pow_succ_of_two_le (k := 11) hx
  calc x ^ 18 = x ^ 7 * x ^ 11 := by ring
    _ ≤ (x ^ 8 - 1) * (x ^ 12 - 1) := Nat.mul_le_mul (by omega) (by omega)

theorem mul_self_sub_one_eq {y : ℕ} (hy : 1 ≤ y) : y * y - 1 = (y - 1) * (y + 1) := by
  have hyy : 1 ≤ y * y := by nlinarith
  zify [hy, hyy]
  ring

theorem hne_of_strict_bound {a u : ℕ}
    (h : ∀ g : ℕ, 1 ≤ g → a = 9 * g → u < (2 ^ (6 * g) - 1) * (2 ^ (9 * g) - 1)) :
    ∀ g : ℕ, 1 ≤ g → a = 9 * g →
      u ≠ (2 ^ (6 * g) - 1) * (2 ^ (9 * g) - 1) ∧ u ≠ (2 ^ (6 * g) - 1) * (2 ^ (9 * g) + 1) := by
  intro g hg hag
  have h1 := h g hg hag
  have h2 : (2 ^ (6 * g) - 1) * (2 ^ (9 * g) - 1) ≤ (2 ^ (6 * g) - 1) * (2 ^ (9 * g) + 1) :=
    Nat.mul_le_mul_left _ (le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _))
  exact ⟨h1.ne, (h1.trans_le h2).ne⟩

theorem not_isTypeEpsCube_of_pow_mul {X : Type} [Group X] {m d u : ℕ} (hu : Odd u)
    (hX : Nat.card X = (2 ^ m) ^ d * u) (hsmall : u < (2 ^ m) ^ (5 * d))
    (hne : ∀ g : ℕ, 1 ≤ g → d * m = 9 * g → u < (2 ^ (6 * g) - 1) * (2 ^ (9 * g) - 1)) :
    ¬ IsTypeEpsCube X := by
  have e : ∀ k : ℕ, (2 ^ m) ^ k = 2 ^ (k * m) := fun k => by rw [← pow_mul, mul_comm]
  refine not_isTypeEpsCube_of_two_adic (a := d * m) hu ?_ ?_ (hne_of_strict_bound hne)
  · rw [hX, e d]
  · calc u < (2 ^ m) ^ (5 * d) := hsmall
      _ = 2 ^ (5 * (d * m)) := by rw [e, mul_assoc]

theorem not_isTypeEpsCube_of_card_sp4_even {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : Nat.card X = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) :
    ¬ IsTypeEpsCube X := by
  have hx1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  refine not_isTypeEpsCube_of_pow_mul (d := 4)
    (u := ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) ?_ hX ?_ ?_
  · exact (odd_two_pow_pow_sub_one hm (k := 2) (by norm_num)).mul
      (odd_two_pow_pow_sub_one hm (k := 4) (by norm_num))
  · calc ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) ≤ (2 ^ m) ^ (2 + 4) :=
          sub_one_mul_sub_one_le_pow _ _ _
      _ < (2 ^ m) ^ (5 * 4) := Nat.pow_lt_pow_right hx1 (by norm_num)
  · intro g _ hdg
    have hA : (2 ^ m) ^ 4 = 2 ^ (9 * g) := by rw [← hdg, ← pow_mul, mul_comm]
    have hB : (2 ^ m) ^ 2 < 2 ^ (6 * g) := by
      rw [← pow_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h1 : (2 ^ m) ^ 2 - 1 < 2 ^ (6 * g) - 1 := by
      have : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    have h2 : 0 < 2 ^ (9 * g) - 1 := by
      have : 1 < 2 ^ (9 * g) := Nat.one_lt_two_pow (by omega)
      omega
    rw [hA]
    exact Nat.mul_lt_mul_of_pos_right h1 h2

theorem not_isTypeEpsCube_of_card_g2_even {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : Nat.card X = (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) :
    ¬ IsTypeEpsCube X := by
  have hx1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have hx2 : 2 ≤ 2 ^ m := by omega
  have hlt8 : (2 ^ m) ^ 8 < (2 ^ m) ^ (5 * 6) := Nat.pow_lt_pow_right hx1 (by norm_num)
  refine not_isTypeEpsCube_of_pow_mul (d := 6)
    (u := ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) ?_ hX
    (lt_of_le_of_lt (sub_one_mul_sub_one_le_pow (2 ^ m) 6 2) hlt8) ?_
  · exact (odd_two_pow_pow_sub_one hm (k := 6) (by norm_num)).mul
      (odd_two_pow_pow_sub_one hm (k := 2) (by norm_num))
  · intro g _ hdg
    have hA : (2 ^ m) ^ 6 = 2 ^ (9 * g) := by rw [← hdg, ← pow_mul, mul_comm]
    have h46 : 4 * m = 6 * g := by omega
    have hB : (2 ^ m) ^ 4 = 2 ^ (6 * g) := by rw [← h46, ← pow_mul, mul_comm]
    have h1 : (2 ^ m) ^ 2 - 1 < (2 ^ m) ^ 4 - 1 := by
      have : (2 ^ m) ^ 2 < (2 ^ m) ^ 4 := Nat.pow_lt_pow_right hx1 (by norm_num)
      have : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    have h2 : 0 < (2 ^ m) ^ 6 - 1 := by
      have : 2 ≤ (2 ^ m) ^ 6 := le_trans hx2 (Nat.le_self_pow (by norm_num) (2 ^ m))
      omega
    rw [← hA, ← hB]
    exact lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left h1 h2) (mul_comm _ _)

theorem not_isTypeEpsCube_of_card_u4_even {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : Nat.card X = (2 ^ m) ^ 6 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1))) :
    ¬ IsTypeEpsCube X := by
  have hx1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have hx2 : 2 ≤ 2 ^ m := by omega
  have h3 : (2 ^ m) ^ 3 + 1 ≤ (2 ^ m) ^ 4 := add_one_le_pow_succ_of_two_le (k := 3) hx2
  have hu10 : ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1) ≤ (2 ^ m) ^ 10 :=
    calc ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1)
        ≤ (2 ^ m) ^ 2 * (2 ^ m) ^ 4 * (2 ^ m) ^ 4 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le _ _) h3) (Nat.sub_le _ _)
      _ = (2 ^ m) ^ 10 := by ring
  have hlt10 : (2 ^ m) ^ 10 < (2 ^ m) ^ (5 * 6) := Nat.pow_lt_pow_right hx1 (by norm_num)
  refine not_isTypeEpsCube_of_pow_mul (d := 6)
    (u := ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1)) ?_ hX
    (lt_of_le_of_lt hu10 hlt10) ?_
  · exact ((odd_two_pow_pow_sub_one hm (k := 2) (by norm_num)).mul
      (odd_two_pow_pow_add_one hm (k := 3) (by norm_num))).mul
      (odd_two_pow_pow_sub_one hm (k := 4) (by norm_num))
  · intro g _ hdg
    have hA : (2 ^ m) ^ 6 = 2 ^ (9 * g) := by rw [← hdg, ← pow_mul, mul_comm]
    have h46 : 4 * m = 6 * g := by omega
    have hB : (2 ^ m) ^ 4 = 2 ^ (6 * g) := by rw [← h46, ← pow_mul, mul_comm]
    have hfac : (2 ^ m) ^ 6 - 1 = ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 3 + 1) := by
      rw [show (2 ^ m) ^ 6 = (2 ^ m) ^ 3 * (2 ^ m) ^ 3 by ring]
      exact mul_self_sub_one_eq (Nat.one_le_pow _ _ (by positivity))
    have h23 : (2 ^ m) ^ 2 - 1 < (2 ^ m) ^ 3 - 1 := by
      have : (2 ^ m) ^ 2 < (2 ^ m) ^ 3 := Nat.pow_lt_pow_right hx1 (by norm_num)
      have : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    have key : ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) < (2 ^ m) ^ 6 - 1 := by
      rw [hfac]
      exact Nat.mul_lt_mul_of_pos_right h23 (by positivity)
    have hR : 0 < (2 ^ m) ^ 4 - 1 := by
      have : 2 ≤ (2 ^ m) ^ 4 := le_trans hx2 (Nat.le_self_pow (by norm_num) (2 ^ m))
      omega
    rw [← hA, ← hB]
    calc ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1)
        < ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 4 - 1) := Nat.mul_lt_mul_of_pos_right key hR
      _ = ((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 6 - 1) := mul_comm _ _

theorem not_isTypeEpsCube_of_card_f4_even {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : Nat.card X = (2 ^ m) ^ 12 * (((2 ^ m) ^ 6 + 1) * ((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 3 + 1) *
      (2 ^ m - 1))) : ¬ IsTypeEpsCube X := by
  have hx1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have hx2 : 2 ≤ 2 ^ m := by omega
  have h7 : (2 ^ m) ^ 6 + 1 ≤ (2 ^ m) ^ 7 := add_one_le_pow_succ_of_two_le (k := 6) hx2
  have h4 : (2 ^ m) ^ 3 + 1 ≤ (2 ^ m) ^ 4 := add_one_le_pow_succ_of_two_le (k := 3) hx2
  have hu16 : ((2 ^ m) ^ 6 + 1) * ((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 3 + 1) * (2 ^ m - 1) ≤
      (2 ^ m) ^ 16 :=
    calc ((2 ^ m) ^ 6 + 1) * ((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 3 + 1) * (2 ^ m - 1)
        ≤ (2 ^ m) ^ 7 * (2 ^ m) ^ 4 * (2 ^ m) ^ 4 * 2 ^ m :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h7 (Nat.sub_le _ _)) h4)
            (Nat.sub_le _ _)
      _ = (2 ^ m) ^ 16 := by ring
  have hlt60 : (2 ^ m) ^ 16 < (2 ^ m) ^ (5 * 12) := Nat.pow_lt_pow_right hx1 (by norm_num)
  have hlt18 : (2 ^ m) ^ 16 < (2 ^ m) ^ 18 := Nat.pow_lt_pow_right hx1 (by norm_num)
  refine not_isTypeEpsCube_of_pow_mul (d := 12)
    (u := ((2 ^ m) ^ 6 + 1) * ((2 ^ m) ^ 4 - 1) * ((2 ^ m) ^ 3 + 1) * (2 ^ m - 1)) ?_ hX
    (lt_of_le_of_lt hu16 hlt60) ?_
  · exact (((odd_two_pow_pow_add_one hm (k := 6) (by norm_num)).mul
      (odd_two_pow_pow_sub_one hm (k := 4) (by norm_num))).mul
      (odd_two_pow_pow_add_one hm (k := 3) (by norm_num))).mul (odd_two_pow_sub_one hm)
  · intro g _ hdg
    have hA : (2 ^ m) ^ 12 = 2 ^ (9 * g) := by rw [← hdg, ← pow_mul, mul_comm]
    have h86 : 8 * m = 6 * g := by omega
    have hB : (2 ^ m) ^ 8 = 2 ^ (6 * g) := by rw [← h86, ← pow_mul, mul_comm]
    rw [← hA, ← hB]
    exact lt_of_le_of_lt hu16 (lt_of_lt_of_le hlt18 (pow_eighteen_le_sub_mul hx2))

end CFSG.RankThree.PartTwo.Sec4.RonanEps
