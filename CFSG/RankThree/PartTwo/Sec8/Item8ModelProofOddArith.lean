module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

open CFSG.RankThree.PartTwo.KFacts

theorem poly_lin {q : ℕ} (hq : 5 ≤ q) :
    27 * (2 * (q + 1) ^ 2) ^ 8 ≤ (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : 1 ≤ (t + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 5) ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have : (0 : ℤ) ≤ (((t : ℤ) + 5) ^ 3 * ((((t : ℤ) + 5) ^ 2 - 1) * (((t : ℤ) + 5) ^ 3 - 1))) ^ 3 -
      27 * (2 * ((t : ℤ) + 5 + 1) ^ 2) ^ 8 := by
    ring_nf
    positivity
  linarith

theorem poly_unit {q : ℕ} (hq : 5 ≤ q) :
    27 * (2 * (q + 1) ^ 2) ^ 8 ≤ (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) ^ 3 := by
  rw [← mul_assoc]
  exact OddChar.poly_su3 hq

theorem poly_l2 {q : ℕ} (hq : 5 ≤ q) :
    2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) < (q ^ 3 - 1) * ((q ^ 3 - 1) ^ 2 - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : 1 ≤ (t + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 5) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ ((t + 5) ^ 3 - 1) ^ 2 := Nat.one_le_pow _ _ (by
    have : 125 ≤ (t + 5) ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ (t + 5) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega)
  zify [h1, h2, h3]
  have : (0 : ℤ) < (((t : ℤ) + 5) ^ 3 - 1) * ((((t : ℤ) + 5) ^ 3 - 1) ^ 2 - 1) -
      2 * (((t : ℤ) + 5) ^ 3 * ((((t : ℤ) + 5) ^ 2 - 1) * (((t : ℤ) + 5) ^ 3 + 1))) := by
    ring_nf
    positivity
  linarith

theorem poly_sl4 {p : ℕ} (hp : 5 ≤ p) :
    3 * (p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1))) <
      (p ^ 2) ^ 3 * (((p ^ 2) ^ 2 - 1) * ((p ^ 2) ^ 3 - 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 5 := ⟨p - 5, by omega⟩
  have h2 : 1 ≤ (t + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (t + 5) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (t + 5) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h22 : 1 ≤ ((t + 5) ^ 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h23 : 1 ≤ ((t + 5) ^ 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h3, h4, h22, h23]
  have : (0 : ℤ) < ((((t : ℤ) + 5) ^ 2) ^ 3 * (((((t : ℤ) + 5) ^ 2) ^ 2 - 1) *
      ((((t : ℤ) + 5) ^ 2) ^ 3 - 1))) - 3 * (((t : ℤ) + 5) ^ 6 * (((((t : ℤ) + 5) ^ 2 - 1) *
      (((t : ℤ) + 5) ^ 3 - 1)) * (((t : ℤ) + 5) ^ 4 - 1))) := by
    ring_nf
    positivity
  linarith

theorem poly_g2p {p : ℕ} (hp : 5 ≤ p) :
    3 * (p ^ 6 * ((p ^ 6 - 1) * (p ^ 2 - 1))) <
      (p ^ 2) ^ 3 * (((p ^ 2) ^ 2 - 1) * ((p ^ 2) ^ 3 - 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 5 := ⟨p - 5, by omega⟩
  have h2 : 1 ≤ (t + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ (t + 5) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h22 : 1 ≤ ((t + 5) ^ 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h23 : 1 ≤ ((t + 5) ^ 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h6, h22, h23]
  have : (0 : ℤ) < ((((t : ℤ) + 5) ^ 2) ^ 3 * (((((t : ℤ) + 5) ^ 2) ^ 2 - 1) *
      ((((t : ℤ) + 5) ^ 2) ^ 3 - 1))) -
      3 * (((t : ℤ) + 5) ^ 6 * ((((t : ℤ) + 5) ^ 6 - 1) * (((t : ℤ) + 5) ^ 2 - 1))) := by
    ring_nf
    positivity
  linarith

theorem three_not_dvd_aux (t : ℕ) :
    ¬ 3 ∣ 3 * t + 2 ∧ ¬ 3 ∣ 3 * t + 1 ∧ ¬ 3 ∣ 3 * t ^ 2 + 3 * t + 1 := by
  refine ⟨by omega, by omega, fun h => ?_⟩
  have : 3 ∣ 3 * (t ^ 2 + t) := dvd_mul_right 3 _
  omega

theorem three_pow_dvd_of_dvd_mul {v A B : ℕ} (hB : ¬ 3 ∣ B) (h : 3 ^ v ∣ A * B) : 3 ^ v ∣ A :=
  (Nat.Coprime.pow_left v
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hB)).dvd_of_dvd_mul_right h

theorem prime_pow_le_lin {q ℓ v : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) (h3 : ¬ 3 ∣ q) (hℓ : ℓ.Prime)
    (h : ℓ ^ v ∣ (q ^ 2 - 1) * (q ^ 3 - 1)) :
    ℓ ^ v ≤ 3 * (q + 1) ^ 2 ∧ (ℓ ≠ 3 → ℓ ^ v ≤ 2 * (q + 1) ^ 2) := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hsq : q ^ 2 - 1 ≤ (q + 1) ^ 2 := by
    have : q ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have hA : q ^ 2 - 1 ≠ 0 := by
      have : 25 ≤ q ^ 2 := by nlinarith
      omega
    have hB : q ^ 3 - 1 ≠ 0 := by
      have : 125 ≤ q ^ 3 := by
        calc 125 = 5 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
      omega
    have hv : v ≤ padicValNat 2 ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      (padicValNat_dvd_iff_le (mul_ne_zero hA hB)).mp h
    rw [padicValNat.mul hA hB] at hv
    have hle : 2 ^ v ≤ 2 * (q + 1) ^ 2 :=
      calc 2 ^ v ≤ 2 ^ (padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 3 - 1)) :=
            Nat.pow_le_pow_right (by norm_num) hv
        _ ≤ 2 * (q ^ 2 - 1) := OddChar.two_pow_padicValNat_sl_three_le hq (by omega)
        _ ≤ 2 * (q + 1) ^ 2 := Nat.mul_le_mul_left _ hsq
    exact ⟨by omega, fun _ => hle⟩
  by_cases hℓ3 : ℓ = 3
  · subst hℓ3
    refine ⟨?_, fun h' => absurd rfl h'⟩
    rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with hq1 | hq1
    · obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
      have hid : ((3 * t + 1) ^ 2 - 1) * ((3 * t + 1) ^ 3 - 1) =
          3 * (3 * t + 1 - 1) ^ 2 * ((3 * t + 2) * (3 * t ^ 2 + 3 * t + 1)) := by
        have e2 : 1 ≤ (3 * t + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        have e3 : 1 ≤ (3 * t + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
        zify [e2, e3]
        push_cast
        ring
      rw [hid] at h
      obtain ⟨n1, -, n3⟩ := three_not_dvd_aux t
      have h' := three_pow_dvd_of_dvd_mul
        (fun hd => (Nat.prime_three.dvd_mul.mp hd).elim (three_not_dvd_aux t).1 n3) h
      have ht : 0 < 3 * t + 1 - 1 := by omega
      calc 3 ^ v ≤ 3 * (3 * t + 1 - 1) ^ 2 := Nat.le_of_dvd (by positivity) h'
        _ ≤ 3 * (3 * t + 1 + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    · obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
      rw [sl3Order_factor (by omega)] at h
      have hnd : ¬ 3 ∣ (3 * t + 2 - 1) ^ 2 * ((3 * t + 2) ^ 2 + (3 * t + 2) + 1) := by
        intro hd
        rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
        · have := Nat.prime_three.dvd_of_dvd_pow hd
          omega
        · have : (3 * t + 2) ^ 2 + (3 * t + 2) + 1 = 3 * (3 * t ^ 2 + 5 * t + 2) + 1 := by ring
          omega
      have h' := three_pow_dvd_of_dvd_mul hnd h
      calc 3 ^ v ≤ 3 * t + 2 + 1 := Nat.le_of_dvd (by omega) h'
        _ ≤ 3 * (3 * t + 2 + 1) ^ 2 := by nlinarith
  · have hle : ℓ ^ v ≤ (q + 1) ^ 2 :=
      le_of_prime_pow_dvd_sl3OddPart hℓ hℓ2 hℓ3 (by omega) (by rwa [← sl3Order_factor (by omega)])
    exact ⟨by omega, fun _ => by omega⟩

theorem su3Order_factor {q : ℕ} (hq : 1 ≤ q) :
    (q ^ 2 - 1) * (q ^ 3 + 1) = (q - 1) * ((q + 1) ^ 2 * (q ^ 2 - q + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h3 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  zify [hq, h2, h3]
  ring

theorem prime_pow_le_unit {q ℓ v : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) (h3 : ¬ 3 ∣ q) (hℓ : ℓ.Prime)
    (h : ℓ ^ v ∣ (q ^ 2 - 1) * (q ^ 3 + 1)) :
    ℓ ^ v ≤ 3 * (q + 1) ^ 2 ∧ (ℓ ≠ 3 → ℓ ^ v ≤ 2 * (q + 1) ^ 2) := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have hA : q ^ 2 - 1 ≠ 0 := by
      have : 25 ≤ q ^ 2 := by nlinarith
      omega
    have hB : q ^ 3 + 1 ≠ 0 := by omega
    have hv : v ≤ padicValNat 2 ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      (padicValNat_dvd_iff_le (mul_ne_zero hA hB)).mp h
    rw [padicValNat.mul hA hB] at hv
    have hle : 2 ^ v ≤ 2 * (q + 1) ^ 2 :=
      calc 2 ^ v ≤ 2 ^ (padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 3 + 1)) :=
            Nat.pow_le_pow_right (by norm_num) hv
        _ ≤ 2 * (q + 1) ^ 2 := OddChar.two_pow_padicValNat_su3_le hq (by omega)
    exact ⟨by omega, fun _ => hle⟩
  rw [su3Order_factor (by omega)] at h
  by_cases hℓ3 : ℓ = 3
  · subst hℓ3
    refine ⟨?_, fun h' => absurd rfl h'⟩
    rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with hq1 | hq1
    · obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
      have hnd : ¬ 3 ∣ (3 * t + 1 + 1) ^ 2 * ((3 * t + 1) ^ 2 - (3 * t + 1) + 1) := by
        intro hd
        rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
        · have := Nat.prime_three.dvd_of_dvd_pow hd
          omega
        · have : (3 * t + 1) ^ 2 - (3 * t + 1) + 1 = 3 * (3 * t ^ 2 + t) + 1 := by
            have e : (3 * t + 1) ^ 2 = 3 * (3 * t ^ 2 + t) + (3 * t + 1) := by ring
            omega
          omega
      have h' := (Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        hnd)).dvd_of_dvd_mul_right h
      calc 3 ^ v ≤ 3 * t + 1 - 1 := Nat.le_of_dvd (by omega) h'
        _ ≤ 3 * t + 1 + 1 := by omega
        _ ≤ (3 * t + 1 + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
        _ ≤ 3 * (3 * t + 1 + 1) ^ 2 := by omega
    · obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
      have hid : (3 * t + 2 - 1) * ((3 * t + 2 + 1) ^ 2 * ((3 * t + 2) ^ 2 - (3 * t + 2) + 1)) =
          3 * (3 * t + 2 + 1) ^ 2 * ((3 * t + 1) * (3 * t ^ 2 + 3 * t + 1)) := by
        have e : (3 * t + 2) ^ 2 - (3 * t + 2) + 1 = 3 * (3 * t ^ 2 + 3 * t + 1) := by
          have e' : (3 * t + 2) ^ 2 = 3 * (3 * t ^ 2 + 3 * t + 1) + (3 * t + 2) - 1 := by
            ring_nf; omega
          omega
        rw [e, show 3 * t + 2 - 1 = 3 * t + 1 by omega]
        ring
      rw [hid] at h
      obtain ⟨-, n1, n3⟩ := three_not_dvd_aux t
      have h' := three_pow_dvd_of_dvd_mul
        (fun hd => (Nat.prime_three.dvd_mul.mp hd).elim n1 n3) h
      exact Nat.le_of_dvd (by positivity) h'
  · have hcases := prime_pow_dvd_of_dvd_mul_three (v := v) hℓ
      (fun ⟨h1, h2⟩ => by
        have h2' := hℓ.dvd_of_dvd_pow h2
        have : ℓ ∣ (q + 1) - (q - 1) := Nat.dvd_sub h2' h1
        rw [show (q + 1) - (q - 1) = 2 by omega] at this
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this))
      (fun ⟨h1, h2⟩ => by
        have hid : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
          zify [hqq, (by omega : 1 ≤ q)]
          ring
        rw [hid] at h2
        have := (Nat.dvd_add_right (Dvd.dvd.mul_left h1 q)).mp h2
        exact hℓ.one_lt.ne' (Nat.dvd_one.mp this))
      (fun ⟨h1, h2⟩ => by
        have h1' := hℓ.dvd_of_dvd_pow h1
        have hid : q ^ 2 - q + 1 = (q + 1) * (q - 2) + 3 := by
          zify [hqq, (by omega : 2 ≤ q)]
          ring
        rw [hid] at h2
        have := (Nat.dvd_add_right (Dvd.dvd.mul_right h1' (q - 2))).mp h2
        exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp this)) h
    have hle : ℓ ^ v ≤ (q + 1) ^ 2 := by
      have hexp : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
      have hq1 : q - 1 ≤ (q + 1) ^ 2 := by omega
      have hq3 : q ^ 2 - q + 1 ≤ (q + 1) ^ 2 := by omega
      rcases hcases with h' | h' | h'
      · exact (Nat.le_of_dvd (by omega) h').trans hq1
      · exact Nat.le_of_dvd (by positivity) h'
      · exact (Nat.le_of_dvd (by omega) h').trans hq3
    exact ⟨by omega, fun _ => by omega⟩

theorem not_dvd_pow_pow_sub_one {ℓ f j : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hj : 1 ≤ j) :
    ¬ ℓ ∣ (ℓ ^ f) ^ j - 1 := by
  intro h
  have h1 : ℓ ∣ (ℓ ^ f) ^ j := dvd_pow (dvd_pow_self ℓ (by omega)) (by omega)
  have h2 : 1 ≤ (ℓ ^ f) ^ j := Nat.one_le_pow _ _ (pow_pos hℓ.pos f)
  have : ℓ ∣ (ℓ ^ f) ^ j - ((ℓ ^ f) ^ j - 1) := Nat.dvd_sub h1 h
  rw [show (ℓ ^ f) ^ j - ((ℓ ^ f) ^ j - 1) = 1 by omega] at this
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp this)

theorem not_dvd_pow_pow_add_one {ℓ f j : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hj : 1 ≤ j) :
    ¬ ℓ ∣ (ℓ ^ f) ^ j + 1 := by
  intro h
  have h1 : ℓ ∣ (ℓ ^ f) ^ j := dvd_pow (dvd_pow_self ℓ (by omega)) (by omega)
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem dvd_and_padicValNat_of_mul {N ℓ a d Y : ℕ} (hℓ : ℓ.Prime) (hd : ¬ ℓ ∣ d)
    (hY : ¬ ℓ ∣ Y) (h : N * d = ℓ ^ a * Y) : ℓ ^ a ∣ N ∧ padicValNat ℓ N = a := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hd0 : d ≠ 0 := fun h0 => hd (h0 ▸ dvd_zero ℓ)
  have hY0 : Y ≠ 0 := fun h0 => hY (h0 ▸ dvd_zero ℓ)
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact mul_ne_zero (pow_ne_zero _ hℓ.ne_zero) hY0 h.symm
  have hcop : Nat.Coprime (ℓ ^ a) d :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hd)
  refine ⟨hcop.dvd_of_dvd_mul_right ⟨Y, h⟩, ?_⟩
  have hv := congrArg (padicValNat ℓ) h
  rw [padicValNat.mul hN0 hd0, padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) hY0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hd,
    padicValNat.eq_zero_of_not_dvd hY] at hv
  omega

structure ModelPart (N ℓ a : ℕ) : Prop where
  prime : ℓ.Prime
  eq : ∃ d Y, ¬ ℓ ∣ d ∧ ¬ ℓ ∣ Y ∧ N * d = ℓ ^ a * Y
  small : N ^ 3 < ℓ ^ (8 * a)

structure L3Data (N p e : ℕ) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  one_le : 1 ≤ e
  le_two : e ≤ 2
  eq : ∃ d X, (d = 1 ∨ d = 3) ∧
    (X = ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) ∨ X = ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) ∧
    N * d = (p ^ e) ^ 3 * X

namespace L3Data

variable {N p e : ℕ}

theorem q_facts (h : L3Data N p e) : Odd (p ^ e) ∧ 5 ≤ p ^ e ∧ ¬ 3 ∣ p ^ e := by
  refine ⟨(h.prime.odd_of_ne_two (by have := h.five_le; omega)).pow,
    le_trans h.five_le (Nat.le_self_pow (by have := h.one_le; omega) p), fun h3 => ?_⟩
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  have := h.five_le
  omega

theorem not_dvd (h : L3Data N p e) {d X : ℕ} (hd : d = 1 ∨ d = 3)
    (hX : X = ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) ∨ X = ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :
    ¬ p ∣ d ∧ ¬ p ∣ X := by
  have hp := h.prime
  have he := h.one_le
  have h5 := h.five_le
  refine ⟨fun hpd => ?_, fun hpX => ?_⟩
  · rcases hd with rfl | rfl
    · exact hp.one_lt.ne' (Nat.dvd_one.mp hpd)
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd
      omega
  · rcases hX with rfl | rfl <;> rcases hp.dvd_mul.mp hpX with h1 | h1
    · exact not_dvd_pow_pow_sub_one hp he (by norm_num) h1
    · exact not_dvd_pow_pow_sub_one hp he (by norm_num) h1
    · exact not_dvd_pow_pow_sub_one hp he (by norm_num) h1
    · exact not_dvd_pow_pow_add_one hp he (by norm_num) h1

theorem padicValNat_eq (h : L3Data N p e) : (p ^ e) ^ 3 ∣ N ∧ padicValNat p N = 3 * e := by
  obtain ⟨d, X, hd, hX, hN⟩ := h.eq
  obtain ⟨hpd, hpX⟩ := h.not_dvd hd hX
  rw [← pow_mul] at hN ⊢
  obtain ⟨h1, h2⟩ := dvd_and_padicValNat_of_mul h.prime hpd hpX hN
  exact ⟨h1, by rw [h2]; ring⟩

theorem le_unit (h : L3Data N p e) : N ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  obtain ⟨d, X, hd, hX, hN⟩ := h.eq
  have hXle : X ≤ ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) := by
    rcases hX with rfl | rfl
    · exact Nat.mul_le_mul_left _ (by omega)
    · exact le_rfl
  calc N ≤ N * d := Nat.le_mul_of_pos_right _ (by rcases hd with rfl | rfl <;> norm_num)
    _ = (p ^ e) ^ 3 * X := hN
    _ ≤ _ := Nat.mul_le_mul_left _ hXle

theorem lin_le (h : L3Data N p e) :
    (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ≤ 3 * N := by
  obtain ⟨d, X, hd, hX, hN⟩ := h.eq
  have hXle : ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) ≤ X := by
    rcases hX with rfl | rfl
    · exact le_rfl
    · exact Nat.mul_le_mul_left _ (by omega)
  calc (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ≤ (p ^ e) ^ 3 * X :=
        Nat.mul_le_mul_left _ hXle
    _ = N * d := hN.symm
    _ ≤ N * 3 := Nat.mul_le_mul_left _ (by rcases hd with rfl | rfl <;> norm_num)
    _ = 3 * N := mul_comm _ _

theorem bound (h : L3Data N p e) :
    ∃ B, B ^ 8 ≤ N ^ 3 ∧ ∀ ℓ v, ℓ.Prime → ℓ ≠ p → ℓ ^ v ∣ N → ℓ ^ v ≤ B := by
  obtain ⟨hqo, hq5, hq3⟩ := h.q_facts
  obtain ⟨d, X, hd, hX, hN⟩ := h.eq
  set q := p ^ e with hq
  have hpoly : 27 * (2 * (q + 1) ^ 2) ^ 8 ≤ (q ^ 3 * X) ^ 3 := by
    rcases hX with rfl | rfl
    · exact poly_lin hq5
    · exact poly_unit hq5
  have hpow : ∀ ℓ v, ℓ.Prime → ℓ ≠ p → ℓ ^ v ∣ q ^ 3 * X →
      ℓ ^ v ≤ 3 * (q + 1) ^ 2 ∧ (ℓ ≠ 3 → ℓ ^ v ≤ 2 * (q + 1) ^ 2) := by
    intro ℓ v hℓ hℓp hdvd
    have hℓq : ¬ ℓ ∣ q := fun h' =>
      hℓp ((Nat.prime_dvd_prime_iff_eq hℓ h.prime).mp (hℓ.dvd_of_dvd_pow h'))
    have hcop : Nat.Coprime (ℓ ^ v) (q ^ 3) :=
      Nat.Coprime.pow v 3 ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓq)
    have hX' := hcop.dvd_of_dvd_mul_left hdvd
    rcases hX with rfl | rfl
    · exact prime_pow_le_lin hqo hq5 hq3 hℓ hX'
    · exact prime_pow_le_unit hqo hq5 hq3 hℓ hX'
  rcases hd with rfl | rfl
  · refine ⟨3 * (q + 1) ^ 2, ?_, fun ℓ v hℓ hℓp hdvd => (hpow ℓ v hℓ hℓp ?_).1⟩
    · rw [mul_one] at hN
      rw [hN]
      calc (3 * (q + 1) ^ 2) ^ 8 = 6561 * ((q + 1) ^ 2) ^ 8 := by ring
        _ ≤ 6912 * ((q + 1) ^ 2) ^ 8 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 27 * (2 * (q + 1) ^ 2) ^ 8 := by ring
        _ ≤ _ := hpoly
    · rw [← hN, mul_one]
      exact hdvd
  · refine ⟨2 * (q + 1) ^ 2, ?_, fun ℓ v hℓ hℓp hdvd => ?_⟩
    · have : 27 * (2 * (q + 1) ^ 2) ^ 8 ≤ 27 * N ^ 3 := by
        calc 27 * (2 * (q + 1) ^ 2) ^ 8 ≤ (q ^ 3 * X) ^ 3 := hpoly
          _ = (N * 3) ^ 3 := by rw [hN]
          _ = 27 * N ^ 3 := by ring
      omega
    · by_cases hℓ3 : ℓ = 3
      · subst hℓ3
        have h1 : 3 ^ (v + 1) ∣ q ^ 3 * X := by
          rw [← hN, pow_succ]
          exact mul_dvd_mul_right hdvd 3
        have h2 := (hpow 3 (v + 1) Nat.prime_three hℓp h1).1
        rw [pow_succ] at h2
        omega
      · exact (hpow ℓ v hℓ hℓp ((Dvd.dvd.mul_right hdvd 3).trans ⟨1, by rw [← hN, mul_one]⟩)).2
          hℓ3

theorem eq_of_modelPart (h : L3Data N p e) {ℓ a : ℕ} (hM : ModelPart N ℓ a) :
    ℓ = p ∧ a = 3 * e := by
  obtain ⟨d, Y, hd, hY, hN⟩ := hM.eq
  obtain ⟨hdvd, hval⟩ := dvd_and_padicValNat_of_mul hM.prime hd hY hN
  by_cases hℓp : ℓ = p
  · subst hℓp
    exact ⟨rfl, hval.symm.trans h.padicValNat_eq.2⟩
  · exfalso
    obtain ⟨B, hB, hle⟩ := h.bound
    have h1 := hle ℓ a hM.prime hℓp hdvd
    have h2 : (ℓ ^ a) ^ 8 ≤ B ^ 8 := Nat.pow_le_pow_left h1 8
    have h3 := hM.small
    rw [← pow_mul, mul_comm a 8] at h2
    omega

theorem false_of_psl2 (h : L3Data N p e) {r g : ℕ} (hr : 2 ≤ r) (hg : g ≤ 2)
    (hN : N * g = r * (r ^ 2 - 1)) : False := by
  obtain ⟨hq3, -⟩ := h.padicValNat_eq
  obtain ⟨hqo, hq5, -⟩ := h.q_facts
  have hle := h.le_unit
  set q := p ^ e with hq
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have hdvd : q ^ 3 ∣ r * (r ^ 2 - 1) := hN ▸ Dvd.dvd.mul_right hq3 g
  have hr2 : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    zify [(by omega : 1 ≤ r), Nat.one_le_pow 2 r (by omega)]
    ring
  have hqp : q ^ 3 = p ^ (e * 3) := by rw [hq, ← pow_mul]
  have cop : ∀ {X : ℕ}, ¬ p ∣ X → Nat.Coprime (q ^ 3) X := fun hX => by
    rw [hqp]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hX)
  have hge : q ^ 3 - 1 ≤ r := by
    by_cases hpr : p ∣ r
    · have hnot : ¬ p ∣ r ^ 2 - 1 := by
        intro h'
        have h1 : p ∣ r ^ 2 := dvd_pow hpr (by norm_num)
        have : p ∣ r ^ 2 - (r ^ 2 - 1) := Nat.dvd_sub h1 h'
        rw [show r ^ 2 - (r ^ 2 - 1) = 1 by
          have : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r (by omega)
          omega] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      have := Nat.le_of_dvd (by omega) ((cop hnot).dvd_of_dvd_mul_right hdvd)
      omega
    · have h1 := (cop hpr).dvd_of_dvd_mul_left hdvd
      rw [hr2] at h1
      by_cases hpm : p ∣ r - 1
      · have hpp : ¬ p ∣ r + 1 := by
          intro h'
          have : p ∣ (r + 1) - (r - 1) := Nat.dvd_sub h' hpm
          rw [show (r + 1) - (r - 1) = 2 by omega] at this
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
        have := Nat.le_of_dvd (by omega) ((cop hpp).dvd_of_dvd_mul_right h1)
        omega
      · have := Nat.le_of_dvd (by omega) ((cop hpm).dvd_of_dvd_mul_left h1)
        omega
  have hmono : (q ^ 3 - 1) * ((q ^ 3 - 1) ^ 2 - 1) ≤ r * (r ^ 2 - 1) :=
    Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
  have hlt := poly_l2 hq5
  have : N * g ≤ 2 * N := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hg
  omega

theorem sl4_lt (h : L3Data N p e) (he : e = 2) :
    p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1)) < N := by
  have h1 := h.lin_le
  subst he
  have h2 := poly_sl4 h.five_le
  omega

theorem g2_lt (h : L3Data N p e) (he : e = 2) : p ^ 6 * ((p ^ 6 - 1) * (p ^ 2 - 1)) < N := by
  have h1 := h.lin_le
  subst he
  have h2 := poly_g2p h.five_le
  omega

end L3Data

end CFSG.RankThree.PartTwo.Sec8.Item8ModelProof
