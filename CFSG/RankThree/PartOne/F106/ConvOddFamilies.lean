module

public import CFSG.RankThree.PartOne.F106.ConvOddCore
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Open CFSG.Timmesfeld.Orders

theorem succ_pow_two_sub_one (w : ℕ) : (w + 1) ^ 2 - 1 = w * (w + 2) :=
  Nat.sub_eq_of_eq_add (by ring)
theorem succ_pow_three_sub_one (w : ℕ) : (w + 1) ^ 3 - 1 = w * (w ^ 2 + 3 * w + 3) :=
  Nat.sub_eq_of_eq_add (by ring)
theorem succ_pow_four_sub_one (w : ℕ) : (w + 1) ^ 4 - 1 = w * (w + 2) * (w ^ 2 + 2 * w + 2) :=
  Nat.sub_eq_of_eq_add (by ring)
theorem succ_pow_six_sub_one (w : ℕ) :
    (w + 1) ^ 6 - 1 = (w * (w ^ 2 + 3 * w + 3)) * ((w + 2) * (w ^ 2 + w + 1)) :=
  Nat.sub_eq_of_eq_add (by ring)

theorem ordA_one_w (w : ℕ) : ordA 1 (w + 1) = (w + 1) * (w * (w + 2)) / Nat.gcd 2 w := by
  simp [ordA, succ_pow_two_sub_one]

theorem ordA_two_w (w : ℕ) :
    ordA 2 (w + 1) = (w + 1) ^ 3 * ((w * (w + 2)) * (w * (w ^ 2 + 3 * w + 3))) / Nat.gcd 3 w := by
  simp [ordA, Finset.prod_Icc_succ_top, succ_pow_two_sub_one, succ_pow_three_sub_one]

theorem ordA_three_w (w : ℕ) :
    ordA 3 (w + 1) = (w + 1) ^ 6 * ((w * (w + 2)) * (w * (w ^ 2 + 3 * w + 3)) *
      (w * (w + 2) * (w ^ 2 + 2 * w + 2))) / Nat.gcd 4 w := by
  simp [ordA, Finset.prod_Icc_succ_top, succ_pow_two_sub_one, succ_pow_three_sub_one,
    succ_pow_four_sub_one]

theorem ordTwistedA_two_w (w : ℕ) :
    ordTwistedA 2 (w + 1) = (w + 1) ^ 3 * ((w * (w + 2)) * ((w + 2) * (w ^ 2 + w + 1))) /
      Nat.gcd 3 (w + 2) := by
  unfold ordTwistedA
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} from rfl, Finset.prod_pair (by norm_num),
    toNat_pow_sub_neg_one_pow_of_even (by omega) (by decide),
    toNat_pow_sub_neg_one_pow_of_odd (by decide), succ_pow_two_sub_one]
  have : (w + 1) ^ 3 + 1 = (w + 2) * (w ^ 2 + w + 1) := by ring
  rw [this]

theorem ordTwistedA_three_w (w : ℕ) :
    ordTwistedA 3 (w + 1) = (w + 1) ^ 6 * ((w * (w + 2)) * ((w + 2) * (w ^ 2 + w + 1)) *
      (w * (w + 2) * (w ^ 2 + 2 * w + 2))) / Nat.gcd 4 (w + 2) := by
  unfold ordTwistedA
  rw [show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl, Finset.prod_insert (by norm_num),
    Finset.prod_pair (by norm_num),
    toNat_pow_sub_neg_one_pow_of_even (by omega) (by decide),
    toNat_pow_sub_neg_one_pow_of_odd (by decide),
    toNat_pow_sub_neg_one_pow_of_even (by omega) (by decide), succ_pow_two_sub_one,
    succ_pow_four_sub_one]
  have : (w + 1) ^ 3 + 1 = (w + 2) * (w ^ 2 + w + 1) := by ring
  rw [this]
  norm_num [mul_assoc]

theorem ordBC_two_w (w : ℕ) :
    ordBC 2 (w + 1) = (w + 1) ^ 4 * ((w * (w + 2)) * (w * (w + 2) * (w ^ 2 + 2 * w + 2))) /
      Nat.gcd 2 w := by
  unfold ordBC
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  have h1 : (w + 1) ^ (2 * 1) - 1 = w * (w + 2) := succ_pow_two_sub_one w
  have h2 : (w + 1) ^ (2 * 2) - 1 = w * (w + 2) * (w ^ 2 + 2 * w + 2) := succ_pow_four_sub_one w
  rw [h1, h2]
  simp

theorem ordG2_w (w : ℕ) :
    ordG2 (w + 1) = (w + 1) ^ 6 * ((w * (w ^ 2 + 3 * w + 3)) * ((w + 2) * (w ^ 2 + w + 1))) *
      (w * (w + 2)) := by
  unfold ordG2
  rw [succ_pow_six_sub_one, succ_pow_two_sub_one]

theorem odd_two_add_one (v : ℕ) : Odd (v + v + 1) := ⟨v, by ring⟩
theorem odd_a (v : ℕ) : Odd ((v + v) ^ 2 + 3 * (v + v) + 3) := ⟨2 * v * v + 3 * v + 1, by ring⟩
theorem odd_b (v : ℕ) : Odd ((v + v) ^ 2 + (v + v) + 1) := ⟨2 * v * v + v, by ring⟩
theorem odd_t (v : ℕ) : Odd (2 * v * v + 2 * v + 1) := ⟨v * v + v, by ring⟩

theorem even_of_odd_succ {w : ℕ} (hq : Odd (w + 1)) : Even w := by
  have := Nat.odd_iff.mp hq
  exact Nat.even_iff.mpr (by omega)

theorem false_ordA_one {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ ordA 1 q) (hsize : (ordA 1 q) ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ := even_of_odd_succ hq
  have hd : Nat.gcd 2 (v + v) = 2 := Nat.gcd_eq_left ⟨v, by ring⟩
  have hod : ordA 1 (v + v + 1) * 2 =
      (v + v + 1) * ((v + v) * ((v + v) + 2)) := by
    rw [ordA_one_w, hd]
    exact Nat.div_mul_cancel ⟨2 * (v + v + 1) * (v * (v + 1)), by ring⟩
  refine odd_family_false (w := v + v) (by omega) ⟨v, rfl⟩ hN (A := 2) (s := 1) (c := 0)
    (k0 := 1) (i := 1) (j := 1) (m := 1) (D := 3) (a := 3) (e := 1) (P := v + v + 1)
    hod (by norm_num) (by norm_num) (odd_two_add_one v) (by ring) (by norm_num) ?_ le_rfl le_rfl
    (by norm_num) (by norm_num) (by norm_num) hdvd hsize
  calc (v + v) ^ 3 = (v + v) * (v + v) * (v + v) := by ring
    _ ≤ (v + v + 1) * ((v + v) * ((v + v) + 2)) := by nlinarith [Nat.zero_le v]


theorem low_ordA_two (w : ℕ) :
    w ^ 8 ≤ (w + 1) ^ 3 * ((w * (w + 2)) * (w * (w ^ 2 + 3 * w + 3))) := by
  calc w ^ 8 = w ^ 3 * ((w * w) * (w * w ^ 2)) := by ring
    _ ≤ _ := by gcongr <;> omega

theorem low_ordTwistedA_two (w : ℕ) :
    w ^ 8 ≤ (w + 1) ^ 3 * ((w * (w + 2)) * ((w + 2) * (w ^ 2 + w + 1))) := by
  calc w ^ 8 = w ^ 3 * ((w * w) * (w * w ^ 2)) := by ring
    _ ≤ _ := by gcongr <;> omega

theorem low_ordG2 (w : ℕ) :
    w ^ 14 ≤ (w + 1) ^ 6 * ((w * (w ^ 2 + 3 * w + 3)) * ((w + 2) * (w ^ 2 + w + 1))) *
      (w * (w + 2)) := by
  calc w ^ 14 = w ^ 6 * ((w * w ^ 2) * (w * w ^ 2)) * (w * w) := by ring
    _ ≤ _ := by gcongr <;> omega

theorem low_ordBC_two (w : ℕ) :
    w ^ 10 ≤ (w + 1) ^ 4 * ((w * (w + 2)) * (w * (w + 2) * (w ^ 2 + 2 * w + 2))) := by
  calc w ^ 10 = w ^ 4 * ((w * w) * (w * w * w ^ 2)) := by ring
    _ ≤ _ := by gcongr <;> omega

theorem low_ordTwistedA_three (w : ℕ) :
    w ^ 15 ≤ (w + 1) ^ 6 * ((w * (w + 2)) * ((w + 2) * (w ^ 2 + w + 1)) *
      (w * (w + 2) * (w ^ 2 + 2 * w + 2))) := by
  calc w ^ 15 = w ^ 6 * ((w * w) * (w * w ^ 2) * (w * w * w ^ 2)) := by ring
    _ ≤ _ := by gcongr <;> omega

theorem low_ordA_three (w : ℕ) :
    w ^ 15 ≤ (w + 1) ^ 6 * ((w * (w + 2)) * (w * (w ^ 2 + 3 * w + 3)) *
      (w * (w + 2) * (w ^ 2 + 2 * w + 2))) := by
  calc w ^ 15 = w ^ 6 * ((w * w) * (w * w ^ 2) * (w * w * w ^ 2)) := by ring
    _ ≤ _ := by gcongr <;> omega

theorem false_ordA_two {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ ordA 2 q) (hsize : (ordA 2 q) ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ := even_of_odd_succ hq
  have hod : ordA 2 (v + v + 1) * Nat.gcd 3 (v + v) =
      (v + v + 1) ^ 3 * (((v + v) * ((v + v) + 2)) *
        ((v + v) * ((v + v) ^ 2 + 3 * (v + v) + 3))) := by
    rw [ordA_two_w]
    exact Nat.div_mul_cancel ((Nat.gcd_dvd_right 3 (v + v)).trans
      ⟨(v + v + 1) ^ 3 * (((v + v) + 2) * ((v + v) * ((v + v) ^ 2 + 3 * (v + v) + 3))), by ring⟩)
  refine odd_family_false (w := v + v) (by omega) ⟨v, rfl⟩ hN (A := 3) (s := 0) (c := 0)
    (k0 := 4) (i := 2) (j := 1) (m := 2) (D := 8) (a := 4) (e := 5)
    (P := (v + v + 1) ^ 3 * ((v + v) ^ 2 + 3 * (v + v) + 3))
    hod (Nat.gcd_le_left _ (by norm_num)) (by simp)
    (Odd.mul (Odd.pow (odd_two_add_one v)) (odd_a v)) (by ring) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdvd hsize
  exact low_ordA_two (v + v)

theorem false_ordTwistedA_two {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ ordTwistedA 2 q) (hsize : (ordTwistedA 2 q) ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ := even_of_odd_succ hq
  have hod : ordTwistedA 2 (v + v + 1) * Nat.gcd 3 (v + v + 2) =
      (v + v + 1) ^ 3 * (((v + v) * ((v + v) + 2)) *
        (((v + v) + 2) * ((v + v) ^ 2 + (v + v) + 1))) := by
    rw [ordTwistedA_two_w]
    exact Nat.div_mul_cancel ((Nat.gcd_dvd_right 3 (v + v + 2)).trans
      ⟨(v + v + 1) ^ 3 * ((v + v) * (((v + v) + 2) * ((v + v) ^ 2 + (v + v) + 1))), by ring⟩)
  refine odd_family_false (w := v + v) (by omega) ⟨v, rfl⟩ hN (A := 3) (s := 0) (c := 0)
    (k0 := 4) (i := 1) (j := 2) (m := 2) (D := 8) (a := 4) (e := 5)
    (P := (v + v + 1) ^ 3 * ((v + v) ^ 2 + (v + v) + 1))
    hod (Nat.gcd_le_left _ (by norm_num)) (by simp)
    (Odd.mul (Odd.pow (odd_two_add_one v)) (odd_b v)) (by ring) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdvd hsize
  exact low_ordTwistedA_two (v + v)

theorem false_ordG2 {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ ordG2 q) (hsize : (ordG2 q) ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ := even_of_odd_succ hq
  have hod : ordG2 (v + v + 1) * 1 =
      (v + v + 1) ^ 6 * (((v + v) * ((v + v) ^ 2 + 3 * (v + v) + 3)) *
        (((v + v) + 2) * ((v + v) ^ 2 + (v + v) + 1))) * ((v + v) * ((v + v) + 2)) := by
    rw [ordG2_w, mul_one]
  refine odd_family_false (w := v + v) (by omega) ⟨v, rfl⟩ hN (A := 1) (s := 0) (c := 0)
    (k0 := 4) (i := 2) (j := 2) (m := 2) (D := 14) (a := 7) (e := 17)
    (P := (v + v + 1) ^ 6 * (((v + v) ^ 2 + 3 * (v + v) + 3) * ((v + v) ^ 2 + (v + v) + 1)))
    hod (by norm_num) (by simp)
    (Odd.mul (Odd.pow (odd_two_add_one v)) (Odd.mul (odd_a v) (odd_b v))) (by ring)
    (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdvd
    hsize
  exact low_ordG2 (v + v)

theorem false_ordBC_two {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ ordBC 2 q) (hsize : (ordBC 2 q) ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ := even_of_odd_succ hq
  have hd : Nat.gcd 2 (v + v) = 2 := Nat.gcd_eq_left ⟨v, by ring⟩
  have hod : ordBC 2 (v + v + 1) * 2 =
      (v + v + 1) ^ 4 * (((v + v) * ((v + v) + 2)) *
        ((v + v) * ((v + v) + 2) * ((v + v) ^ 2 + 2 * (v + v) + 2))) := by
    rw [ordBC_two_w, hd]
    exact Nat.div_mul_cancel ⟨(v + v + 1) ^ 4 * (v * (((v + v) + 2) *
      ((v + v) * ((v + v) + 2) * ((v + v) ^ 2 + 2 * (v + v) + 2)))), by ring⟩
  refine odd_family_false (w := v + v) (by omega) ⟨v, rfl⟩ hN (A := 2) (s := 1) (c := 1)
    (k0 := 4) (i := 2) (j := 2) (m := 2) (D := 10) (a := 5) (e := 9)
    (P := (v + v + 1) ^ 4 * (2 * v * v + 2 * v + 1))
    hod (by norm_num) (by norm_num)
    (Odd.mul (Odd.pow (odd_two_add_one v)) (odd_t v)) (by ring) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdvd hsize
  exact low_ordBC_two (v + v)

theorem false_ordTwistedA_three {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ ordTwistedA 3 q) (hsize : (ordTwistedA 3 q) ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ := even_of_odd_succ hq
  have hod : ordTwistedA 3 (v + v + 1) * Nat.gcd 4 (v + v + 2) =
      (v + v + 1) ^ 6 * (((v + v) * ((v + v) + 2)) *
        (((v + v) + 2) * ((v + v) ^ 2 + (v + v) + 1)) *
        ((v + v) * ((v + v) + 2) * ((v + v) ^ 2 + 2 * (v + v) + 2))) := by
    rw [ordTwistedA_three_w]
    exact Nat.div_mul_cancel ((Nat.gcd_dvd_right 4 (v + v + 2)).trans
      ⟨(v + v + 1) ^ 6 * ((v + v) * (((v + v) + 2) * ((v + v) ^ 2 + (v + v) + 1)) *
        ((v + v) * ((v + v) + 2) * ((v + v) ^ 2 + 2 * (v + v) + 2))), by ring⟩)
  refine odd_family_false (w := v + v) (by omega) ⟨v, rfl⟩ hN (A := 4) (s := 0) (c := 1)
    (k0 := 7) (i := 2) (j := 3) (m := 3) (D := 15) (a := 5) (e := 9)
    (P := (v + v + 1) ^ 6 * (((v + v) ^ 2 + (v + v) + 1) * (2 * v * v + 2 * v + 1)))
    hod (Nat.gcd_le_left _ (by norm_num)) (by simp)
    (Odd.mul (Odd.pow (odd_two_add_one v)) (Odd.mul (odd_b v) (odd_t v))) (by ring)
    (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdvd
    hsize
  exact low_ordTwistedA_three (v + v)

theorem false_ordA_three {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ ordA 3 q) (hsize : (ordA 3 q) ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ := even_of_odd_succ hq
  have hod : ordA 3 (v + v + 1) * Nat.gcd 4 (v + v) =
      (v + v + 1) ^ 6 * (((v + v) * ((v + v) + 2)) *
        ((v + v) * ((v + v) ^ 2 + 3 * (v + v) + 3)) *
        ((v + v) * ((v + v) + 2) * ((v + v) ^ 2 + 2 * (v + v) + 2))) := by
    rw [ordA_three_w]
    exact Nat.div_mul_cancel ((Nat.gcd_dvd_right 4 (v + v)).trans
      ⟨(v + v + 1) ^ 6 * (((v + v) + 2) * ((v + v) * ((v + v) ^ 2 + 3 * (v + v) + 3)) *
        ((v + v) * ((v + v) + 2) * ((v + v) ^ 2 + 2 * (v + v) + 2))), by ring⟩)
  refine odd_family_false (w := v + v) (by omega) ⟨v, rfl⟩ hN (A := 4) (s := 0) (c := 1)
    (k0 := 7) (i := 3) (j := 2) (m := 3) (D := 15) (a := 5) (e := 9)
    (P := (v + v + 1) ^ 6 * (((v + v) ^ 2 + 3 * (v + v) + 3) * (2 * v * v + 2 * v + 1)))
    hod (Nat.gcd_le_left _ (by norm_num)) (by simp)
    (Odd.mul (Odd.pow (odd_two_add_one v)) (Odd.mul (odd_a v) (odd_t v))) (by ring)
    (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdvd
    hsize
  exact low_ordA_three (v + v)

end CFSG.RankThree.PartOne.F106
