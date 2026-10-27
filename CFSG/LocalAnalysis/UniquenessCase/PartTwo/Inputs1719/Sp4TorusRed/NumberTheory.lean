module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Ring.Parity

import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed


lemma four_mul_sub_mul_eq (q k : ℕ) :
    (4 : ℤ) * (1 + (k : ℤ) * ((q : ℤ) - 1) ^ 2)
        - ((k : ℤ) + 1) * ((q : ℤ) + 4 * (k : ℤ) + 2) * ((q : ℤ) + 2 * (k : ℤ))
      = 16 * (k : ℤ) ^ 3 + 18 * (k : ℤ) ^ 2 * ((q : ℤ) - 4 * (k : ℤ))
        - 92 * (k : ℤ) ^ 2 + 3 * (k : ℤ) * ((q : ℤ) - 4 * (k : ℤ)) ^ 2
        - 24 * (k : ℤ) * ((q : ℤ) - 4 * (k : ℤ)) - 8 * (k : ℤ)
        - ((q : ℤ) - 4 * (k : ℤ)) ^ 2 - 2 * ((q : ℤ) - 4 * (k : ℤ)) + 4 := by
  ring

lemma four_mul_sub_mul_pos_of_six_le (k b : ℕ) (hk : 6 ≤ k) :
    0 < 16 * (k : ℤ) ^ 3 + 18 * (k : ℤ) ^ 2 * (b : ℤ)
        - 92 * (k : ℤ) ^ 2 + 3 * (k : ℤ) * (b : ℤ) ^ 2
        - 24 * (k : ℤ) * (b : ℤ) - 8 * (k : ℤ) - (b : ℤ) ^ 2 - 2 * (b : ℤ) + 4 := by
  have hk' : (6 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hb : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have hD : 16 * (k : ℤ) ^ 3 + 18 * (k : ℤ) ^ 2 * (b : ℤ)
        - 92 * (k : ℤ) ^ 2 + 3 * (k : ℤ) * (b : ℤ) ^ 2
        - 24 * (k : ℤ) * (b : ℤ) - 8 * (k : ℤ) - (b : ℤ) ^ 2 - 2 * (b : ℤ) + 4
      = (16 * (k : ℤ) ^ 3 - 92 * (k : ℤ) ^ 2 - 8 * (k : ℤ) + 4)
        + (3 * (k : ℤ) - 1) * (b : ℤ) ^ 2
        + (18 * (k : ℤ) ^ 2 - 24 * (k : ℤ) - 2) * (b : ℤ) := by
    ring
  rw [hD]
  have h0 : 0 < 16 * (k : ℤ) ^ 3 - 92 * (k : ℤ) ^ 2 - 8 * (k : ℤ) + 4 := by
    have hfac : 16 * (k : ℤ) ^ 3 - 92 * (k : ℤ) ^ 2 - 8 * (k : ℤ) + 4
        = 100 + 4 * ((k : ℤ) - 6) * (4 * (k : ℤ) ^ 2 + (k : ℤ) + 4) := by
      ring
    rw [hfac]
    have h1 : (0 : ℤ) ≤ (k : ℤ) - 6 := by linarith
    have h2 : (0 : ℤ) ≤ 4 * (k : ℤ) ^ 2 + (k : ℤ) + 4 := by positivity
    nlinarith [mul_nonneg h1 h2]
  have h1 : 0 ≤ (3 * (k : ℤ) - 1) * (b : ℤ) ^ 2 := by
    have : (0 : ℤ) ≤ 3 * (k : ℤ) - 1 := by linarith
    exact mul_nonneg this (sq_nonneg _)
  have h2 : 0 ≤ (18 * (k : ℤ) ^ 2 - 24 * (k : ℤ) - 2) * (b : ℤ) := by
    have hk2 : (0 : ℤ) ≤ 18 * (k : ℤ) ^ 2 - 24 * (k : ℤ) - 2 := by nlinarith
    exact mul_nonneg hk2 hb
  nlinarith

lemma four_mul_sub_mul_pos_of_one_le_of_nine_le (k b : ℕ) (hk1 : 1 ≤ k) (hb : 9 ≤ b) :
    0 < 16 * (k : ℤ) ^ 3 + 18 * (k : ℤ) ^ 2 * (b : ℤ)
        - 92 * (k : ℤ) ^ 2 + 3 * (k : ℤ) * (b : ℤ) ^ 2
        - 24 * (k : ℤ) * (b : ℤ) - 8 * (k : ℤ) - (b : ℤ) ^ 2 - 2 * (b : ℤ) + 4 := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 9 := ⟨b - 9, by omega⟩
  have hexp : 16 * ((d + 1 : ℕ) : ℤ) ^ 3 + 18 * ((d + 1 : ℕ) : ℤ) ^ 2 * ((c + 9 : ℕ) : ℤ)
        - 92 * ((d + 1 : ℕ) : ℤ) ^ 2 + 3 * ((d + 1 : ℕ) : ℤ) * ((c + 9 : ℕ) : ℤ) ^ 2
        - 24 * ((d + 1 : ℕ) : ℤ) * ((c + 9 : ℕ) : ℤ) - 8 * ((d + 1 : ℕ) : ℤ)
        - ((c + 9 : ℕ) : ℤ) ^ 2 - 2 * ((c + 9 : ℕ) : ℤ) + 4
      = 10 + 16 * (d : ℤ) ^ 3 + 18 * (d : ℤ) ^ 2 * (c : ℤ)
        + 3 * (d : ℤ) * (c : ℤ) ^ 2 + 118 * (d : ℤ) ^ 2 + 66 * (d : ℤ) * (c : ℤ)
        + 2 * (c : ℤ) ^ 2 + 207 * (d : ℤ) + 28 * (c : ℤ) := by
    push_cast
    ring
  rw [hexp]
  positivity

lemma four_mul_lt_of_r_add_one_le (q k r : ℕ) (hq : q = 4 * r) (hr : 2 ≤ r)
    (hkr : r + 1 ≤ k) :
    (q + 1) * (q ^ 2 + 1) < 4 * (1 + k * (q - 1) ^ 2) := by
  subst q
  have hr' : (2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hkr' : (r : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hkr
  have hD : (4 : ℤ) * (1 + (k : ℤ) * ((4 * (r : ℤ)) - 1) ^ 2)
      - ((4 * (r : ℤ)) + 1) * ((4 * (r : ℤ)) ^ 2 + 1)
      = ((4 * (r : ℤ)) - 1) * ((4 * (r : ℤ)) - 7)
        + 4 * ((4 * (r : ℤ)) - 1) ^ 2 * ((k : ℤ) - (r : ℤ) - 1) := by
    ring
  have hfirst : 0 < ((4 * (r : ℤ)) - 1) * ((4 * (r : ℤ)) - 7) := by
    apply mul_pos <;> nlinarith
  have hsecond : 0 ≤ 4 * ((4 * (r : ℤ)) - 1) ^ 2 * ((k : ℤ) - (r : ℤ) - 1) := by
    have hk' : 0 ≤ (k : ℤ) - (r : ℤ) - 1 := by linarith
    positivity
  have hDpos : 0 < (4 : ℤ) * (1 + (k : ℤ) * ((4 * (r : ℤ)) - 1) ^ 2)
      - ((4 * (r : ℤ)) + 1) * ((4 * (r : ℤ)) ^ 2 + 1) := by
    rw [hD]
    linarith
  have hcast : ((4 * r - 1 : ℕ) : ℤ) = 4 * (r : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * r)]
    push_cast
    ring
  have hZ : (((4 * r + 1) * ((4 * r) ^ 2 + 1) : ℕ) : ℤ)
      < ((4 * (1 + k * (4 * r - 1) ^ 2) : ℕ) : ℤ) := by
    push_cast
    rw [hcast]
    linarith
  exact_mod_cast hZ

lemma gcd_pow_four_dvd_succ {n k N : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hkq : k ≤ 2 ^ n / 4) (hN : N = 1 + k * (2 ^ n - 1) ^ 2) :
    Nat.gcd ((2 ^ n) ^ 4) N ∣ k + 1 := by
  set q : ℕ := 2 ^ n with hq
  have hNq : N = 1 + k * (q - 1) ^ 2 := by simpa [← hq] using hN
  have hkq' : k ≤ q / 4 := by simpa [← hq] using hkq
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq_pos : 0 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hqsub : q - 2 + 2 = q := Nat.sub_add_cancel hq2
  have hqm : q = (q - 1) + 1 := by omega
  have hm2 : (q - 1) ^ 2 = q * (q - 2) + 1 := by nlinarith
  have hNalt : N = (k + 1) + k * (q * (q - 2)) := by
    rw [hNq, hm2]
    ring
  have h2dvdq : 2 ^ (n + 1) ∣ q * (q - 2) := by
    have hq2' : q - 2 = 2 * (2 ^ (n - 1) - 1) := by
      have h2n : q = 2 * 2 ^ (n - 1) := by
        rw [hq, ← Nat.pow_sub_mul_pow 2 (by omega : 1 ≤ n), pow_one]
        ring
      rw [h2n]
      simpa using (Nat.mul_sub_left_distrib 2 (2 ^ (n - 1)) 1).symm
    refine ⟨2 ^ (n - 1) - 1, ?_⟩
    rw [hq, hq2']
    calc 2 ^ n * (2 * (2 ^ (n - 1) - 1))
        = (2 ^ n * 2) * (2 ^ (n - 1) - 1) := by ring
      _ = 2 ^ (n + 1) * (2 ^ (n - 1) - 1) := by rw [pow_succ]
  have hApow : Nat.gcd (q ^ 4) N ∣ 2 ^ (4 * n) := by
    have hqpow : q ^ 4 = 2 ^ (4 * n) := by
      rw [hq, ← pow_mul, Nat.mul_comm]
    rw [hqpow]
    exact Nat.gcd_dvd_left _ _
  obtain ⟨j, hjle, hAeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hApow
  have hjle_n : j ≤ n := by
    by_contra hjn
    have hj : n + 1 ≤ j := by omega
    have h2A : 2 ^ (n + 1) ∣ Nat.gcd (q ^ 4) N := by
      rw [hAeq]
      exact Nat.pow_dvd_pow 2 hj
    have h2N : 2 ^ (n + 1) ∣ N := h2A.trans (Nat.gcd_dvd_right _ _)
    have h2k : 2 ^ (n + 1) ∣ k * (q * (q - 2)) := dvd_mul_of_dvd_right h2dvdq k
    have h2k1 : 2 ^ (n + 1) ∣ k + 1 := by
      rw [hNalt] at h2N
      exact (Nat.dvd_add_iff_left h2k).mpr h2N
    have hlt : k + 1 < 2 ^ (n + 1) := by
      have hq4pow : q / 4 = 2 ^ (n - 2) := by
        have hq_eq : q = 4 * 2 ^ (n - 2) := by
          rw [hq, show n = (n - 2) + 2 by omega, pow_add]
          norm_num
          ring
        have hdvd : 4 ∣ q := ⟨2 ^ (n - 2), hq_eq⟩
        have hdiv : q / 4 * 4 = q := Nat.div_mul_cancel hdvd
        have hqdiv : q = 4 * (q / 4) := by
          rw [mul_comm]
          exact hdiv.symm
        have h4 : 4 * (q / 4) = 4 * 2 ^ (n - 2) := by rw [← hqdiv, hq_eq]
        exact Nat.mul_left_cancel (by norm_num : 0 < 4) h4
      have h2n : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
        calc 2 ^ (n - 1) = 2 ^ ((n - 2) + 1) := by
              rw [show n - 1 = (n - 2) + 1 by omega]
          _ = 2 ^ (n - 2) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (n - 2) := by ring
      have hstep : 2 ^ (n - 1) < 2 ^ (n + 1) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hge : 1 ≤ 2 ^ (n - 2) := by
        have := pow_pos (by norm_num : 0 < 2) (n - 2)
        omega
      have hle : k + 1 ≤ q / 4 + 1 := by omega
      rw [hq4pow] at hle
      omega
    have hpos : 0 < k + 1 := by omega
    have := Nat.le_of_dvd hpos h2k1
    omega
  have hAq : Nat.gcd (q ^ 4) N ∣ q := by
    rw [hq, hAeq]
    exact Nat.pow_dvd_pow 2 hjle_n
  have hAq2 : Nat.gcd (q ^ 4) N ∣ q * (q - 2) :=
    hAq.trans (Nat.dvd_mul_right q (q - 2))
  have hAqk : Nat.gcd (q ^ 4) N ∣ k * (q * (q - 2)) := dvd_mul_of_dvd_right hAq2 k
  have hAN : Nat.gcd (q ^ 4) N ∣ N := Nat.gcd_dvd_right _ _
  have hAN' : Nat.gcd (q ^ 4) N ∣ (k + 1) + k * (q * (q - 2)) := by
    rw [← hNalt]
    exact hAN
  exact (Nat.dvd_add_iff_left hAqk).mpr hAN' 

lemma two_mul_gcd_sq_succ_le {n k N : ℕ} (hn : 3 ≤ n)
    (hN : N = 1 + k * (2 ^ n - 1) ^ 2) :
    2 * Nat.gcd ((2 ^ n + 1) ^ 2) N ≤ 2 ^ n + 4 * k + 2 := by
  set q : ℕ := 2 ^ n with hq
  have hNq : N = 1 + k * (q - 1) ^ 2 := by simpa [← hq] using hN
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq_pos : 0 < q := by omega
  have hq_even : Even q := by
    rw [hq]
    exact (by norm_num : Even 2).pow_of_ne_zero (by omega)
  have hs_odd : Odd (q + 1) := hq_even.add_one
  set B : ℕ := Nat.gcd ((q + 1) ^ 2) N with hB
  have hBN : B ∣ N := Nat.gcd_dvd_right _ _
  have hBs2 : B ∣ (q + 1) ^ 2 := Nat.gcd_dvd_left _ _
  have hBodd : Odd B := by
    have hs2odd : Odd ((q + 1) ^ 2) := hs_odd.pow
    obtain ⟨t, ht⟩ := hBs2
    rw [ht] at hs2odd
    exact Nat.Odd.of_mul_left hs2odd
  have hBdvd : B ∣ q + 4 * k + 2 := by
    let sZ : ℤ := (q : ℤ) + 1
    have hBNZ : (B : ℤ) ∣ (N : ℤ) := by exact_mod_cast hBN
    have hBs2Z : (B : ℤ) ∣ sZ ^ 2 := by
      have h : (((q + 1) ^ 2 : ℕ) : ℤ) = sZ ^ 2 := by
        push_cast
        simp [sZ]
      rw [← h]
      exact_mod_cast hBs2
    have hq1 : 1 ≤ q := by omega
    have hNZ : (N : ℤ) = 1 + (k : ℤ) * (sZ - 2) ^ 2 := by
      rw [hNq]
      have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
        rw [Nat.cast_sub hq1]
        push_cast
        ring
      push_cast
      rw [hqsub]
      simp only [sZ]
      ring
    have h1 : (B : ℤ) ∣ 1 + (k : ℤ) * (sZ - 2) ^ 2 := by
      rw [← hNZ]
      exact hBNZ
    have h2 : (B : ℤ) ∣ (k : ℤ) * sZ ^ 2 := dvd_mul_of_dvd_right hBs2Z (k : ℤ)
    have h3 : (B : ℤ) ∣ 1 + 4 * (k : ℤ) - 4 * (k : ℤ) * sZ := by
      have hsub : (1 + (k : ℤ) * (sZ - 2) ^ 2) - (k : ℤ) * sZ ^ 2
          = 1 + 4 * (k : ℤ) - 4 * (k : ℤ) * sZ := by
        ring
      rw [← hsub]
      exact dvd_sub h1 h2
    have h4 : (B : ℤ) ∣ sZ * (1 + 4 * (k : ℤ)) := by
      have h : sZ * (1 + 4 * (k : ℤ))
          = sZ * (1 + 4 * (k : ℤ) - 4 * (k : ℤ) * sZ) + 4 * (k : ℤ) * sZ ^ 2 := by
        ring
      rw [h]
      exact dvd_add (by simpa [mul_comm] using dvd_mul_of_dvd_left h3 sZ)
        (dvd_mul_of_dvd_right hBs2Z (4 * (k : ℤ)))
    have h5 : (B : ℤ) ∣ (q : ℤ) + 4 * (k : ℤ) + 2 := by
      have h : (q : ℤ) + 4 * (k : ℤ) + 2
          = (1 + 4 * (k : ℤ) - 4 * (k : ℤ) * sZ) + sZ * (1 + 4 * (k : ℤ)) := by
        simp [sZ]
        ring
      rw [h]
      exact dvd_add h3 h4
    exact_mod_cast h5
  have hXeven : Even (q + 4 * k + 2) := by
    have h4k : Even (4 * k + 2) := ⟨2 * k + 1, by ring⟩
    exact hq_even.add h4k
  have h2B : 2 * B ≤ q + 4 * k + 2 := by
    have hcop : Nat.Coprime B 2 := Nat.coprime_two_right.mpr hBodd
    have h2dvd : 2 ∣ q + 4 * k + 2 := hXeven.two_dvd
    have h2Bdvd : B * 2 ∣ q + 4 * k + 2 := hcop.mul_dvd_of_dvd_of_dvd hBdvd h2dvd
    have hpos : 0 < q + 4 * k + 2 := by omega
    have := Nat.le_of_dvd hpos h2Bdvd
    omega
  exact h2B

lemma two_mul_gcd_sq_add_one_le {n k N : ℕ} (hn : 3 ≤ n)
    (hN : N = 1 + k * (2 ^ n - 1) ^ 2) :
    2 * Nat.gcd ((2 ^ n) ^ 2 + 1) N ≤ 2 ^ n + 2 * k := by
  set q : ℕ := 2 ^ n with hq
  have hNq : N = 1 + k * (q - 1) ^ 2 := by simpa [← hq] using hN
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq_pos : 0 < q := by omega
  have hq_even : Even q := by
    rw [hq]
    exact (by norm_num : Even 2).pow_of_ne_zero (by omega)
  have hq2p1_odd : Odd (q ^ 2 + 1) := by
    have hq2_even : Even (q ^ 2) := hq_even.pow_of_ne_zero (by norm_num)
    exact hq2_even.add_one
  set C : ℕ := Nat.gcd (q ^ 2 + 1) N with hC
  have hCN : C ∣ N := Nat.gcd_dvd_right _ _
  have hCq2 : C ∣ q ^ 2 + 1 := Nat.gcd_dvd_left _ _
  have hCodd : Odd C := by
    obtain ⟨t, ht⟩ := hCq2
    rw [ht] at hq2p1_odd
    exact Nat.Odd.of_mul_left hq2p1_odd
  have hCdvd : C ∣ q + 2 * k := by
    let qZ : ℤ := (q : ℤ)
    have hCNZ : (C : ℤ) ∣ (N : ℤ) := by exact_mod_cast hCN
    have hCq2Z : (C : ℤ) ∣ qZ ^ 2 + 1 := by
      have h : (((q ^ 2 + 1 : ℕ)) : ℤ) = qZ ^ 2 + 1 := by
        simp [qZ]
      rw [← h]
      exact_mod_cast hCq2
    have hq1 : 1 ≤ q := by omega
    have hqsub : ((q - 1 : ℕ) : ℤ) = qZ - 1 := by
      rw [Nat.cast_sub hq1]
      simp [qZ]
    have hNZ : (N : ℤ) = 1 + (k : ℤ) * (qZ - 1) ^ 2 := by
      rw [hNq]
      push_cast
      rw [hqsub]
    have h1 : (C : ℤ) ∣ 1 - 2 * (k : ℤ) * qZ := by
      have hkq2 : (C : ℤ) ∣ (k : ℤ) * (qZ ^ 2 + 1) :=
        dvd_mul_of_dvd_right hCq2Z (k : ℤ)
      have hNsub : (N : ℤ) - (k : ℤ) * (qZ ^ 2 + 1) = 1 - 2 * (k : ℤ) * qZ := by
        rw [hNZ]
        ring
      rw [← hNsub]
      exact dvd_sub hCNZ hkq2
    have h2 : (C : ℤ) ∣ qZ + 2 * (k : ℤ) := by
      have h3 : (C : ℤ) ∣ qZ * (1 - 2 * (k : ℤ) * qZ) := by
        simpa [mul_comm] using dvd_mul_of_dvd_left h1 qZ
      have h4 : (C : ℤ) ∣ 2 * (k : ℤ) * (qZ ^ 2 + 1) :=
        dvd_mul_of_dvd_right hCq2Z (2 * (k : ℤ))
      have hsum : qZ * (1 - 2 * (k : ℤ) * qZ) + 2 * (k : ℤ) * (qZ ^ 2 + 1)
          = qZ + 2 * (k : ℤ) := by
        ring
      rw [← hsum]
      exact dvd_add h3 h4
    have h2' : (C : ℤ) ∣ (q : ℤ) + ((2 * k : ℕ) : ℤ) := by simpa [qZ] using h2
    exact_mod_cast h2'
  have hXeven : Even (q + 2 * k) := by
    have h2k : Even (2 * k) := ⟨k, by ring⟩
    exact hq_even.add h2k
  have h2C : 2 * C ≤ q + 2 * k := by
    have hcop : Nat.Coprime C 2 := Nat.coprime_two_right.mpr hCodd
    have h2dvd : 2 ∣ q + 2 * k := hXeven.two_dvd
    have h2Cdvd : C * 2 ∣ q + 2 * k := hcop.mul_dvd_of_dvd_of_dvd hCdvd h2dvd
    have hpos : 0 < q + 2 * k := by omega
    have := Nat.le_of_dvd hpos h2Cdvd
    omega
  exact h2C

lemma gcd_mul_gcd_mul_gcd_eq {n N : ℕ} (hn : 3 ≤ n)
    (hdvd : N ∣ (2 ^ n) ^ 4 * (2 ^ n + 1) ^ 2 * ((2 ^ n) ^ 2 + 1)) :
    N = Nat.gcd ((2 ^ n) ^ 4) N * Nat.gcd ((2 ^ n + 1) ^ 2) N
      * Nat.gcd ((2 ^ n) ^ 2 + 1) N := by
  set q : ℕ := 2 ^ n with hq
  have hdvdq : N ∣ q ^ 4 * (q + 1) ^ 2 * (q ^ 2 + 1) := by simpa [← hq] using hdvd
  have hq_even : Even q := by
    rw [hq]
    exact (by norm_num : Even 2).pow_of_ne_zero (by omega)
  have hq1 : 1 ≤ q := by
    rw [hq]
    have := pow_pos (by norm_num : 0 < 2) n
    omega
  have hqs : Nat.Coprime q (q + 1) :=
    (Nat.coprime_self_add_right (m := q) (n := 1)).2 (Nat.coprime_one_right q)
  have hcopQS : Nat.Coprime (q ^ 4) ((q + 1) ^ 2) := by
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 4)]
    rw [Nat.coprime_pow_right_iff (by norm_num : 0 < 2)]
    exact hqs
  have hcopQ2 : Nat.Coprime (q ^ 4) (q ^ 2 + 1) := by
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 4)]
    have hq2 : q ^ 2 + 1 = 1 + q * q := by ring
    rw [hq2]
    exact (Nat.coprime_add_mul_left_right q 1 q).2 (by simp)
  have hcopQ : Nat.Coprime (q ^ 4) ((q + 1) ^ 2 * (q ^ 2 + 1)) :=
    hcopQS.mul_right hcopQ2
  have hq2id : q ^ 2 + 1 = (q + 1) * (q - 1) + 2 := by
    have hZ : (((q ^ 2 + 1 : ℕ)) : ℤ) = (((q + 1) * (q - 1) + 2 : ℕ) : ℤ) := by
      have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
        rw [Nat.cast_sub hq1]
        push_cast
        ring
      push_cast
      rw [hqsub]
      ring
    exact_mod_cast hZ
  have hqS2 : Nat.Coprime (q + 1) 2 := Nat.coprime_two_right.mpr hq_even.add_one
  have hcopS0 : Nat.Coprime (q + 1) (q ^ 2 + 1) := by
    rw [hq2id]
    exact (Nat.coprime_mul_left_add_right (q + 1) 2 (q - 1)).2 hqS2
  have hcopS : Nat.Coprime ((q + 1) ^ 2) (q ^ 2 + 1) := by
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
    exact hcopS0
  set A : ℕ := Nat.gcd (q ^ 4) N with hA
  set B : ℕ := Nat.gcd ((q + 1) ^ 2) N with hB
  set C : ℕ := Nat.gcd (q ^ 2 + 1) N with hC
  set D : ℕ := Nat.gcd ((q + 1) ^ 2 * (q ^ 2 + 1)) N with hD
  have hdvdX : N ∣ q ^ 4 * ((q + 1) ^ 2 * (q ^ 2 + 1)) := by
    simpa only [mul_assoc] using hdvdq
  have hN_AD : N = A * D := by
    calc N = Nat.gcd (q ^ 4 * ((q + 1) ^ 2 * (q ^ 2 + 1))) N :=
          (Nat.gcd_eq_right hdvdX).symm
      _ = Nat.gcd (q ^ 4) N * Nat.gcd ((q + 1) ^ 2 * (q ^ 2 + 1)) N :=
          hcopQ.mul_gcd N
      _ = A * D := rfl
  have hD_X : D ∣ (q + 1) ^ 2 * (q ^ 2 + 1) := Nat.gcd_dvd_left _ _
  have hB_eq : Nat.gcd ((q + 1) ^ 2) D = B := by
    calc Nat.gcd ((q + 1) ^ 2) D
        = Nat.gcd ((q + 1) ^ 2) (Nat.gcd ((q + 1) ^ 2 * (q ^ 2 + 1)) N) := by rw [hD]
      _ = Nat.gcd (Nat.gcd ((q + 1) ^ 2) ((q + 1) ^ 2 * (q ^ 2 + 1))) N :=
          (Nat.gcd_assoc ((q + 1) ^ 2) ((q + 1) ^ 2 * (q ^ 2 + 1)) N).symm
      _ = Nat.gcd ((q + 1) ^ 2) N := by
          rw [Nat.gcd_eq_left (Nat.dvd_mul_right ((q + 1) ^ 2) (q ^ 2 + 1))]
      _ = B := rfl
  have hC_eq : Nat.gcd (q ^ 2 + 1) D = C := by
    calc Nat.gcd (q ^ 2 + 1) D
        = Nat.gcd (q ^ 2 + 1) (Nat.gcd ((q + 1) ^ 2 * (q ^ 2 + 1)) N) := by rw [hD]
      _ = Nat.gcd (Nat.gcd (q ^ 2 + 1) ((q + 1) ^ 2 * (q ^ 2 + 1))) N :=
          (Nat.gcd_assoc (q ^ 2 + 1) ((q + 1) ^ 2 * (q ^ 2 + 1)) N).symm
      _ = Nat.gcd (q ^ 2 + 1) N := by
          rw [Nat.gcd_eq_left (Nat.dvd_mul_left (q ^ 2 + 1) ((q + 1) ^ 2))]
      _ = C := rfl
  have hD_BC : D = B * C := by
    calc D = Nat.gcd ((q + 1) ^ 2 * (q ^ 2 + 1)) D := (Nat.gcd_eq_right hD_X).symm
      _ = Nat.gcd ((q + 1) ^ 2) D * Nat.gcd (q ^ 2 + 1) D := hcopS.mul_gcd D
      _ = B * C := by rw [hB_eq, hC_eq]
  calc N = A * D := hN_AD
    _ = A * (B * C) := by rw [hD_BC]
    _ = A * B * C := by ring

lemma four_mul_lt_of_eq_four_mul (q k r : ℕ) (hq : q = 4 * r) (hr : 8 ≤ r)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    (k + 1) * (q + 4 * k + 2) * (q + 2 * k) < 4 * (1 + k * (q - 1) ^ 2) := by
  subst q
  have h4k : 4 * k ≤ 4 * r := by nlinarith
  have hbcast : ((4 * r - 4 * k : ℕ) : ℤ) = 4 * (r : ℤ) - 4 * (k : ℤ) := by
    rw [Nat.cast_sub h4k]
    push_cast
    ring
  have hDpos : 0 < 16 * (k : ℤ) ^ 3 + 18 * (k : ℤ) ^ 2 * (4 * (r : ℤ) - 4 * (k : ℤ))
      - 92 * (k : ℤ) ^ 2 + 3 * (k : ℤ) * (4 * (r : ℤ) - 4 * (k : ℤ)) ^ 2
      - 24 * (k : ℤ) * (4 * (r : ℤ) - 4 * (k : ℤ)) - 8 * (k : ℤ)
      - (4 * (r : ℤ) - 4 * (k : ℤ)) ^ 2 - 2 * (4 * (r : ℤ) - 4 * (k : ℤ)) + 4 := by
    rw [← hbcast]
    by_cases hk6 : 6 ≤ k
    · exact four_mul_sub_mul_pos_of_six_le k (4 * r - 4 * k) hk6
    · have hk5 : k ≤ 5 := by omega
      have hb9 : 9 ≤ 4 * r - 4 * k := by omega
      exact four_mul_sub_mul_pos_of_one_le_of_nine_le k (4 * r - 4 * k) hk1 hb9
  have hcast : ((4 * r - 1 : ℕ) : ℤ) = 4 * (r : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * r)]
    push_cast
    ring
  have hD := four_mul_sub_mul_eq (4 * r) k
  push_cast at hD
  have hZ : (((k + 1) * (4 * r + 4 * k + 2) * (4 * r + 2 * k) : ℕ) : ℤ)
      < ((4 * (1 + k * (4 * r - 1) ^ 2) : ℕ) : ℤ) := by
    push_cast
    rw [hcast]
    linarith
  exact_mod_cast hZ

theorem eq_one_of_modEq_of_le_of_dvd {n N : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hmod : N ≡ 1 [MOD (2 ^ n - 1) ^ 2]) (hle : 4 * (2 ^ n - 1) * N ≤ (2 ^ n) ^ 4 - 1)
    (hdvd : N ∣ (2 ^ n) ^ 4 * (2 ^ n + 1) ^ 2 * ((2 ^ n) ^ 2 + 1)) : N = 1 := by
  set q : ℕ := 2 ^ n with hq
  set m : ℕ := q - 1 with hm
  set s : ℕ := q + 1 with hs
  have hmodq : N ≡ 1 [MOD m ^ 2] := by simpa [← hq, ← hm] using hmod
  have hleq : 4 * m * N ≤ q ^ 4 - 1 := by simpa [← hq, ← hm] using hle
  have hdvdq : N ∣ q ^ 4 * s ^ 2 * (q ^ 2 + 1) := by simpa [← hq, ← hs] using hdvd
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq_pos : 0 < q := by omega
  have hm_pos : 0 < m := by omega
  have hs_pos : 0 < s := by omega
  have hq_even : Even q := by
    rw [hq]
    exact (by norm_num : Even 2).pow_of_ne_zero (by omega)
  have hs_odd : Odd s := by
    rw [hs]
    exact hq_even.add_one
  have hq2p1_odd : Odd (q ^ 2 + 1) := by
    have : Even (q ^ 2) := hq_even.pow_of_ne_zero (by norm_num)
    exact this.add_one
  have hP_pos : 0 < q ^ 4 * s ^ 2 * (q ^ 2 + 1) := by
    have h1 : 0 < q ^ 4 := pow_pos hq_pos _
    have h2 : 0 < s ^ 2 := pow_pos hs_pos _
    have h3 : 0 < q ^ 2 + 1 := by positivity
    positivity
  have hN_pos : 0 < N := Nat.pos_of_dvd_of_pos hdvdq hP_pos
  have h1N : 1 ≤ N := hN_pos
  have hm2dvd : m ^ 2 ∣ N - 1 := by
    have := (Nat.modEq_iff_dvd' h1N).mp hmodq.symm
    simpa [m] using this
  obtain ⟨k, hk⟩ := hm2dvd
  have hN : N = 1 + k * m ^ 2 := by
    calc N = N - 1 + 1 := (Nat.sub_add_cancel h1N).symm
      _ = m ^ 2 * k + 1 := by rw [hk]
      _ = 1 + k * m ^ 2 := by ring
  have hq4 : q ^ 4 - 1 = m * s * (q ^ 2 + 1) := by
    have hq1 : 1 ≤ q ^ 4 := by
      have := pow_pos hq_pos 4
      omega
    rw [Nat.sub_eq_iff_eq_add hq1]
    have hqm : q = m + 1 := by omega
    have hsm : s = m + 2 := by omega
    rw [hqm, hsm]
    ring
  have h4N : 4 * N ≤ s * (q ^ 2 + 1) := by
    have hle' : 4 * m * N ≤ m * (s * (q ^ 2 + 1)) := by
      calc 4 * m * N ≤ q ^ 4 - 1 := hleq
        _ = m * s * (q ^ 2 + 1) := hq4
        _ = m * (s * (q ^ 2 + 1)) := by ring
    have h' : m * (4 * N) ≤ m * (s * (q ^ 2 + 1)) := by
      calc m * (4 * N) = 4 * m * N := by ring
        _ ≤ m * (s * (q ^ 2 + 1)) := hle'
    exact Nat.le_of_mul_le_mul_left h' hm_pos
  have hq_eq_four : q = 4 * (q / 4) := by
    have hdiv : 4 ∣ q := by
      rw [hq]
      exact ⟨2 ^ (n - 2), by
        rw [show n = (n - 2) + 2 by omega, pow_add]
        norm_num
        ring⟩
    have := Nat.div_mul_cancel hdiv
    rw [mul_comm] at this
    exact this.symm
  have hr2 : 2 ≤ q / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by omega)
  have hk_le : k ≤ q / 4 := by
    by_contra hle'
    have hlt : q / 4 < k := Nat.lt_of_not_ge hle'
    have hq_lt : q < 4 * k := by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).mp hlt
      omega
    have hrk : q / 4 + 1 ≤ k := by omega
    have hcontr := four_mul_lt_of_r_add_one_le q k (q / 4) hq_eq_four hr2 hrk
    have h4N' : 4 * (1 + k * (q - 1) ^ 2) ≤ s * (q ^ 2 + 1) := by
      have := h4N
      rw [hN] at this
      simpa [m] using this
    have hcontr' : s * (q ^ 2 + 1) < 4 * (1 + k * (q - 1) ^ 2) := by
      simpa [hs] using hcontr
    omega
  by_cases hk0 : k = 0
  · rw [hk0] at hN
    simpa using hN
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
    have hN' : N = 1 + k * (2 ^ n - 1) ^ 2 := by simpa [← hq, ← hm] using hN
    have hkq' : k ≤ 2 ^ n / 4 := by simpa [← hq] using hk_le
    set A : ℕ := Nat.gcd (q ^ 4) N with hA
    set B : ℕ := Nat.gcd (s ^ 2) N with hB
    set C : ℕ := Nat.gcd (q ^ 2 + 1) N with hC
    have hNfac : N = A * B * C := by
      have h := gcd_mul_gcd_mul_gcd_eq (n := n) (N := N) hn hdvd
      simpa [← hq, ← hs, hA, hB, hC] using h
    have hA_dvd : A ∣ k + 1 := by
      have h := gcd_pow_four_dvd_succ (n := n) (k := k) (N := N) hn hk1 hkq' hN'
      simpa [← hA, ← hq] using h
    have hB_le : 2 * B ≤ q + 4 * k + 2 := by
      have h := two_mul_gcd_sq_succ_le (n := n) (k := k) (N := N) hn hN'
      simpa [← hB, ← hq, ← hs] using h
    have hC_le : 2 * C ≤ q + 2 * k := by
      have h := two_mul_gcd_sq_add_one_le (n := n) (k := k) (N := N) hn hN'
      simpa [← hC, ← hq] using h
    have hA_le : A ≤ k + 1 := Nat.le_of_dvd (by omega) hA_dvd
    have h4Nle : 4 * N ≤ (k + 1) * (q + 4 * k + 2) * (q + 2 * k) := by
      calc 4 * N = A * (2 * B) * (2 * C) := by rw [hNfac]; ring
        _ ≤ (k + 1) * (q + 4 * k + 2) * (q + 2 * k) := by gcongr
    by_cases hn3 : n = 3
    · have hq_eq_8 : q = 8 := by rw [hq, hn3]; norm_num
      have hm7 : m = 7 := by omega
      have hs9 : s = 9 := by omega
      have hk_le2 : k ≤ 2 := by omega
      interval_cases k
      · have hN50 : N = 50 := by
          rw [hN, hm7]
          norm_num
        exfalso
        have h50 : 50 ∣ 8 ^ 4 * 9 ^ 2 * (8 ^ 2 + 1) := by
          have h := hdvdq
          rw [hN50, hq_eq_8, hs9] at h
          exact h
        norm_num at h50
      · have hN99 : N = 99 := by
          rw [hN, hm7]
          norm_num
        exfalso
        have h99 : 99 ∣ 8 ^ 4 * 9 ^ 2 * (8 ^ 2 + 1) := by
          have h := hdvdq
          rw [hN99, hq_eq_8, hs9] at h
          exact h
        norm_num at h99
    · have hn5 : 5 ≤ n := by
        rcases hodd with ⟨a, ha⟩
        omega
      have hq32 : 32 ≤ q := by
        rw [hq]
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn5
      have hr8 : 8 ≤ q / 4 :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by omega)
      have hlt := four_mul_lt_of_eq_four_mul q k (q / 4) hq_eq_four hr8 hk1 hk_le
      have h4Nle' : 4 * (1 + k * (q - 1) ^ 2) ≤ (k + 1) * (q + 4 * k + 2) * (q + 2 * k) := by
        have h := h4Nle
        rw [hN] at h
        simpa [m] using h
      exfalso
      exact (not_le_of_gt hlt) h4Nle'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
