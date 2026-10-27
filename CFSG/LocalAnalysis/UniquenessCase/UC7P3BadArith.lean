module

public import Mathlib.Data.Nat.Notation
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

@[expose] def ThreeHeavy (n : ℕ) : Prop :=
  ∃ k m : ℕ, n = 3 ^ k * m ∧ m < (3 ^ k) ^ 2

theorem ThreeHeavy.exists {n : ℕ} (h : ThreeHeavy n) :
    ∃ k : ℕ, 3 ^ k ∣ n ∧ n < (3 ^ k) ^ 3 := by
  obtain ⟨k, m, rfl, hm⟩ := h
  refine ⟨k, dvd_mul_right _ _, ?_⟩
  calc 3 ^ k * m < 3 ^ k * (3 ^ k) ^ 2 := Nat.mul_lt_mul_of_pos_left hm (by positivity)
    _ = (3 ^ k) ^ 3 := by ring

theorem threeHeavy_linTwo {a n : ℕ} (h : n = 3 ^ a * (((3 ^ a) ^ 2 - 1) / 2)) :
    ThreeHeavy n := by
  refine ⟨a, _, h, ?_⟩
  have h1 : 1 ≤ (3 ^ a) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  generalize (3 ^ a) ^ 2 = y at h1 ⊢
  omega

theorem threeHeavy_cube {a m n : ℕ} (h : n = (3 ^ a) ^ 3 * m) (hm : m < ((3 ^ a) ^ 3) ^ 2) :
    ThreeHeavy n :=
  ⟨a * 3, m, by rw [h, pow_mul], by rw [pow_mul]; exact hm⟩

theorem unitary_cofactor_lt {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 3 + 1) * (q ^ 2 - 1) < (q ^ 3) ^ 2 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ^ 2 ≤ q ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : 2 * q ^ 5 ≤ q ^ 6 := by
    calc 2 * q ^ 5 ≤ q * q ^ 5 := Nat.mul_le_mul_right _ hq
      _ = q ^ 6 := by ring
  have h4 : (q ^ 3 + 1) * (q ^ 2 - 1) + (q ^ 3 + 1) = q ^ 5 + q ^ 2 := by
    have : (q ^ 3 + 1) * (q ^ 2 - 1) + (q ^ 3 + 1) = (q ^ 3 + 1) * q ^ 2 := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    rw [this]
    ring
  have h5 : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have h6 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

theorem threeHeavy_unitary {a n : ℕ} (ha : 1 ≤ a)
    (h : n * Nat.gcd 3 (3 ^ a + 1) = (3 ^ a) ^ 3 * ((3 ^ a) ^ 3 + 1) * ((3 ^ a) ^ 2 - 1)) :
    ThreeHeavy n := by
  have h3 : 3 ∣ 3 ^ a := dvd_pow_self 3 (by omega)
  have hg : Nat.gcd 3 (3 ^ a + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  rw [hg, mul_one] at h
  refine threeHeavy_cube (by rw [h, mul_assoc]) ?_
  have hq : 2 ≤ 3 ^ a := by
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  exact unitary_cofactor_lt hq

theorem threeHeavy_ree {e n : ℕ} (he : 1 ≤ e)
    (h : n = (3 ^ e) ^ 3 * ((3 ^ e) ^ 3 + 1) * (3 ^ e - 1)) : ThreeHeavy n := by
  refine threeHeavy_cube (by rw [h, mul_assoc]) ?_
  have hq : 2 ≤ 3 ^ e := by
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  generalize 3 ^ e = q at hq ⊢
  have h1 : (q ^ 3 + 1) * (q - 1) ≤ (q ^ 3 + 1) * (q ^ 2 - 1) := by
    refine Nat.mul_le_mul_left _ ?_
    have : q ^ 2 = q * q := by ring
    have : q ≤ q * q := Nat.le_mul_self q
    omega
  exact lt_of_le_of_lt h1 (unitary_cofactor_lt hq)

theorem three_mul_pow_six_le {q : ℕ} (hq : 5 ≤ q) :
    3 * (q + 1) ^ 6 ≤ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) := by
  have ha : (5 * (q + 1)) ^ 6 ≤ (6 * q) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  rw [mul_pow, mul_pow] at ha
  have hb : (q + 1) ^ 6 ≤ 3 * q ^ 6 := by
    generalize (q + 1) ^ 6 = A at ha ⊢
    generalize q ^ 6 = B at ha ⊢
    norm_num at ha
    omega
  have hc : 9 ≤ q ^ 2 - 1 := by
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  have hd : 9 * q ^ 6 ≤ q ^ 6 * (q ^ 2 - 1) := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hc
  have he : q ^ 6 * (q ^ 2 - 1) ≤ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) := by
    refine Nat.mul_le_mul_right _ ?_
    calc q ^ 6 = q ^ 3 * q ^ 3 := by ring
      _ ≤ q ^ 3 * (q ^ 3 + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  omega

theorem pow_three_le_of_unitary_order {q n k : ℕ} (hq : 5 ≤ q) (h3 : ¬ 3 ∣ q)
    (h : n * Nat.gcd 3 (q + 1) = q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1)) (hk : 3 ^ k ∣ n) :
    3 ^ k ≤ (q + 1) ^ 2 := by
  have hcop3 : Nat.Coprime 3 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hcopk : ∀ b : ℕ, Nat.Coprime 3 b → Nat.Coprime (3 ^ k) b := fun b hb =>
    Nat.Coprime.pow_left k hb
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hmod with h1 | h2
  ·
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
    have hg : Nat.gcd 3 (3 * t + 1 + 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [hg, mul_one] at h
    have e : (3 * t + 1) ^ 3 * ((3 * t + 1) ^ 3 + 1) * ((3 * t + 1) ^ 2 - 1) =
        (3 * t) * ((3 * t + 1) ^ 3 * ((3 * t + 2) ^ 2 * (9 * t ^ 2 + 3 * t + 1))) := by
      have : (3 * t + 1) ^ 2 - 1 = 3 * t * (3 * t + 2) := by
        have : (3 * t + 1) ^ 2 = 3 * t * (3 * t + 2) + 1 := by ring
        omega
      rw [this]
      ring
    rw [e] at h
    have hdvd : 3 ^ k ∣ (3 * t) * ((3 * t + 1) ^ 3 * ((3 * t + 2) ^ 2 * (9 * t ^ 2 + 3 * t + 1))) :=
      h ▸ hk
    have hc : Nat.Coprime (3 ^ k) ((3 * t + 1) ^ 3 * ((3 * t + 2) ^ 2 * (9 * t ^ 2 + 3 * t + 1))) := by
      refine hcopk _ (Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 hcop3)
        (Nat.Coprime.mul_right (Nat.Coprime.pow_right 2
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))) ?_))
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => ?_
      have : 3 ∣ 9 * t ^ 2 + 3 * t := ⟨3 * t ^ 2 + t, by ring⟩
      have := (Nat.dvd_add_right this).1 hd
      omega
    have := hc.dvd_of_dvd_mul_right hdvd
    calc 3 ^ k ≤ 3 * t := Nat.le_of_dvd (by omega) this
      _ ≤ (3 * t + 1 + 1) ^ 2 := by nlinarith
  ·
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
    have hg : Nat.gcd 3 (3 * t + 2 + 1) = 3 := Nat.gcd_eq_left ⟨t + 1, by ring⟩
    rw [hg] at h
    have e : (3 * t + 2) ^ 3 * ((3 * t + 2) ^ 3 + 1) * ((3 * t + 2) ^ 2 - 1) =
        3 * ((3 * t + 2) ^ 3 * (9 * (t + 1) ^ 2 * ((3 * t + 1) * (3 * t ^ 2 + 3 * t + 1)))) := by
      have : (3 * t + 2) ^ 2 - 1 = (3 * t + 1) * (3 * (t + 1)) := by
        have : (3 * t + 2) ^ 2 = (3 * t + 1) * (3 * (t + 1)) + 1 := by ring
        omega
      rw [this]
      ring
    rw [e, mul_comm n 3] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h
    have hdvd : 3 ^ k ∣ (3 * t + 2) ^ 3 * (9 * (t + 1) ^ 2 * ((3 * t + 1) * (3 * t ^ 2 + 3 * t + 1))) :=
      h' ▸ hk
    have hc1 : Nat.Coprime (3 ^ k) ((3 * t + 2) ^ 3) := hcopk _ (Nat.Coprime.pow_right 3 hcop3)
    have hdvd2 := hc1.dvd_of_dvd_mul_left hdvd
    have hc2 : Nat.Coprime (3 ^ k) ((3 * t + 1) * (3 * t ^ 2 + 3 * t + 1)) := by
      refine hcopk _ (Nat.Coprime.mul_right
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)) ?_)
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => ?_
      have : 3 ∣ 3 * t ^ 2 + 3 * t := ⟨t ^ 2 + t, by ring⟩
      have := (Nat.dvd_add_right this).1 hd
      omega
    have hdvd3 := hc2.dvd_of_dvd_mul_right hdvd2
    have hle : 3 ^ k ≤ 9 * (t + 1) ^ 2 := Nat.le_of_dvd (by positivity) hdvd3
    calc 3 ^ k ≤ 9 * (t + 1) ^ 2 := hle
      _ = (3 * t + 2 + 1) ^ 2 := by ring

theorem not_threeHeavy_unitary {q n : ℕ} (hq : 5 ≤ q) (h3 : ¬ 3 ∣ q)
    (h : n * Nat.gcd 3 (q + 1) = q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1)) : ¬ ThreeHeavy n := by
  intro hH
  obtain ⟨k, hk, hlt⟩ := hH.exists
  have hb := pow_three_le_of_unitary_order hq h3 h hk
  have h6 : ((q + 1) ^ 2) ^ 3 = (q + 1) ^ 6 := by ring
  have h7 : (3 ^ k) ^ 3 ≤ (q + 1) ^ 6 := h6 ▸ Nat.pow_le_pow_left hb 3
  have h8 : n * Nat.gcd 3 (q + 1) ≤ n * 3 :=
    Nat.mul_le_mul_left n (Nat.gcd_le_left (q + 1) (by norm_num))
  have h9 := three_mul_pow_six_le hq
  omega

theorem not_threeHeavy_of_val {n v : ℕ} (hdiv : ¬ 3 ^ (v + 1) ∣ n) (hle : (3 ^ v) ^ 3 ≤ n) :
    ¬ ThreeHeavy n := by
  intro hH
  obtain ⟨k, hk, hlt⟩ := hH.exists
  have hkv : k ≤ v := by
    by_contra h
    exact hdiv ((pow_dvd_pow 3 (by omega : v + 1 ≤ k)).trans hk)
  have h1 : 3 ^ k ≤ 3 ^ v := Nat.pow_le_pow_right (by norm_num) hkv
  have h2 : (3 ^ k) ^ 3 ≤ (3 ^ v) ^ 3 := Nat.pow_le_pow_left h1 3
  omega

theorem not_threeHeavy_mcl : ¬ ThreeHeavy 898128000 :=
  not_threeHeavy_of_val (v := 6) (by norm_num) (by norm_num)

theorem not_threeHeavy_tits : ¬ ThreeHeavy 17971200 :=
  not_threeHeavy_of_val (v := 3) (by norm_num) (by norm_num)

theorem not_threeHeavy_fi22 : ¬ ThreeHeavy 64561751654400 :=
  not_threeHeavy_of_val (v := 9) (by norm_num) (by norm_num)

theorem not_threeHeavy_j4 : ¬ ThreeHeavy 86775571046077562880 :=
  not_threeHeavy_of_val (v := 3) (by norm_num) (by norm_num)

theorem not_threeHeavy_sz32 : ¬ ThreeHeavy 32537600 :=
  not_threeHeavy_of_val (v := 0) (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
