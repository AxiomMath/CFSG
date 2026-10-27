module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129D4H

theorem no_psl2_card_eq_psl3_aux_even {P s S u : ℕ} (hP : 64 ≤ P) (hPs : P ≤ s)
    (hS : s ^ 2 = S + 1) (hE : 3 * (s * S) = P * u) (hu : u + 1 ≤ P * P) : False := by
  have hSP : P * P ≤ S + 1 := by
    rw [← hS, sq]
    exact Nat.mul_le_mul hPs hPs
  have e1 : P * S ≤ s * S := Nat.mul_le_mul_right S hPs
  have e2 : P * (P * P) ≤ P * (S + 1) := Nat.mul_le_mul_left P hSP
  have e3 : P * (u + 1) ≤ P * (P * P) := Nat.mul_le_mul_left P hu
  have e4 : 64 * (P * P) ≤ P * (P * P) := Nat.mul_le_mul_right (P * P) hP
  have e5 : 64 * P ≤ P * P := Nat.mul_le_mul_right P hP
  nlinarith

theorem no_psl2_card_eq_psl3_aux_odd {P s S u : ℕ} (hP : 64 ≤ P) (hPs : P ≤ s + 1)
    (hS : s ^ 2 = S + 1) (hE : 3 * (s * S) = 2 * (P * u)) (hu : u + 1 ≤ P * P) : False := by
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  have hps : p ≤ s := by omega
  have hSP : p * p ≤ S + 1 := by
    rw [← hS, sq]
    exact Nat.mul_le_mul hps hps
  have e1 : p * S ≤ s * S := Nat.mul_le_mul_right S hps
  have e2 : p * (p * p) ≤ p * (S + 1) := Nat.mul_le_mul_left p hSP
  have e3 : (p + 1) * (u + 1) ≤ (p + 1) * ((p + 1) * (p + 1)) :=
    Nat.mul_le_mul_left (p + 1) hu
  have e4 : 63 * (p * p) ≤ p * (p * p) := Nat.mul_le_mul_right (p * p) (by omega)
  have e5 : 63 * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
  nlinarith

theorem no_psl2_card_eq_psl3 {n s N : ℕ} (hn : 2 ≤ n) (hs : 4 ≤ s)
    (hs' : (∃ m, s = 2 ^ m) ∨ Odd s) {t : ℕ}
    (ht : t = (2 ^ n) ^ 3 - 1 ∨ t = (2 ^ n) ^ 3 + 1)
    (hN : N * Nat.gcd 2 (s - 1) = s * (s ^ 2 - 1))
    (hD : 3 * N = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * t)) : False := by
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ n := ⟨_, rfl⟩
  rw [← hq] at ht hD
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨P, hP⟩ : ∃ P, P = q ^ 3 := ⟨_, rfl⟩
  rw [← hP] at ht hD
  have hP64 : 64 ≤ P := by
    rw [hP]
    calc (64 : ℕ) = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
  have hqP : q ^ 2 ≤ P := by
    rw [hP]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hcop : ∀ k : ℕ, k % 2 = 1 → Nat.Coprime P k := by
    intro k hk
    have h2 : Nat.Coprime 2 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
    rw [hP, hq]
    exact Nat.Coprime.pow_left 3 (Nat.Coprime.pow_left n h2)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  obtain ⟨Q, hQ⟩ : ∃ Q, q ^ 2 = Q + 1 := ⟨q ^ 2 - 1, by omega⟩
  rw [show q ^ 2 - 1 = Q by omega] at hD
  have htP : t ≤ P + 1 := by omega
  obtain ⟨u, hu⟩ : ∃ u, Q * t = u := ⟨_, rfl⟩
  rw [hu] at hD
  have huP : u + 1 ≤ P * P := by
    have h1 : (Q + 1) * (P + 1) ≤ P * (P + 1) := Nat.mul_le_mul_right (P + 1) (by omega)
    have h2 : Q * t ≤ Q * (P + 1) := Nat.mul_le_mul_left Q htP
    nlinarith
  have hsq1 : 1 ≤ s ^ 2 := Nat.one_le_pow 2 s (by omega)
  obtain ⟨S, hS⟩ : ∃ S, s ^ 2 = S + 1 := ⟨s ^ 2 - 1, by omega⟩
  rw [show s ^ 2 - 1 = S by omega] at hN
  rcases hs' with ⟨m, hm⟩ | hodd
  ·
    have hse : 2 ∣ s := by
      rw [hm]
      refine dvd_pow_self 2 ?_
      rintro rfl
      rw [pow_zero] at hm
      omega
    have h2 : Nat.Coprime 2 (s - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
    have hg : Nat.gcd 2 (s - 1) = 1 := h2
    rw [hg, mul_one] at hN
    have hse2 : 2 ∣ s ^ 2 := dvd_pow hse (by norm_num)
    have hSodd : S % 2 = 1 := by omega
    have hdiv : P ∣ s * (3 * S) := ⟨u, by rw [← hD, hN]; ring⟩
    have hPs : P ∣ s := Nat.Coprime.dvd_of_dvd_mul_right (hcop (3 * S) (by omega)) hdiv
    exact no_psl2_card_eq_psl3_aux_even hP64 (Nat.le_of_dvd (by omega) hPs) hS
      (by rw [← hN]; exact hD) huP
  ·
    have hs2 : s % 2 = 1 := Nat.odd_iff.mp hodd
    have hg : Nat.gcd 2 (s - 1) = 2 := Nat.gcd_eq_left (by omega)
    rw [hg] at hN
    obtain ⟨a, rfl⟩ := hodd
    have hE : 3 * ((2 * a + 1) * S) = 2 * (P * u) := by
      rw [← hN, ← hD]
      ring
    have hS4 : S = 4 * (a * (a + 1)) := by nlinarith [hS]
    have hkey : P * u = 6 * ((2 * a + 1) * (a * (a + 1))) := by
      rw [hS4] at hN
      nlinarith [hN, hD]
    have hdiv : P ∣ 2 * (a * (a + 1)) * (3 * (2 * a + 1)) :=
      ⟨u, by rw [hkey]; ring⟩
    have hPd : P ∣ 2 * (a * (a + 1)) :=
      Nat.Coprime.dvd_of_dvd_mul_right (hcop (3 * (2 * a + 1)) (by omega)) hdiv
    have hPle : P ≤ 2 * a + 1 + 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · have h1 : P ∣ 2 * a * (a + 1) := by
          have e : 2 * a * (a + 1) = 2 * (a * (a + 1)) := by ring
          rw [e]
          exact hPd
        have h2 : P ∣ 2 * a := Nat.Coprime.dvd_of_dvd_mul_right (hcop (a + 1) (by omega)) h1
        have := Nat.le_of_dvd (by omega) h2
        omega
      · have h1 : P ∣ a * (2 * (a + 1)) := by
          have e : a * (2 * (a + 1)) = 2 * (a * (a + 1)) := by ring
          rw [e]
          exact hPd
        have h2 : P ∣ 2 * (a + 1) := Nat.Coprime.dvd_of_dvd_mul_left (hcop a (by omega)) h1
        have := Nat.le_of_dvd (by omega) h2
        omega
    exact no_psl2_card_eq_psl3_aux_odd hP64 hPle hS hE huP

end CFSG.RankThree.PartTwo.Sec12.Hering129D4H
