module

public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinForms
import CFSG.GH74.GLS.Stage2.Final.ModelArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.GH74.GLS.Stage2.Final.ModelArith

private lemma w183art_not_both_dvd_A_B {ℓ r : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2)
    (ha : ℓ ∣ r + 2) (hb : ℓ ∣ (r + 4) ^ 2) : False := by
  have hb' : ℓ ∣ r + 4 := hℓ.dvd_of_dvd_pow hb
  have h : ℓ ∣ 2 := by
    have hsub := Nat.dvd_sub hb' ha
    simpa using hsub
  exact not_dvd_two hℓ h2 h

private lemma w183art_not_both_dvd_A_C {ℓ r : ℕ} (hℓ : ℓ.Prime)
    (ha : ℓ ∣ r + 2) (hc : ℓ ∣ r ^ 2 + 5 * r + 7) : False := by
  have hC : r ^ 2 + 5 * r + 7 = (r + 2) * (r + 3) + 1 := by ring
  rw [hC] at hc
  have hprod : ℓ ∣ (r + 2) * (r + 3) := Dvd.dvd.mul_right ha _
  have h1 : ℓ ∣ 1 := (Nat.dvd_add_right hprod).1 hc
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)

private lemma w183art_not_both_dvd_B_C_of_five (r : ℕ)
    (hb : 5 ∣ (r + 4) ^ 2) (hc : 5 ∣ r ^ 2 + 5 * r + 7) : False := by
  have hb' : 5 ∣ r + 4 := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow hb
  have hC : r ^ 2 + 5 * r + 7 = (r + 4) * (r + 1) + 3 := by ring
  rw [hC] at hc
  have hprod : 5 ∣ (r + 4) * (r + 1) := Dvd.dvd.mul_right hb' _
  have h3 : 5 ∣ 3 := (Nat.dvd_add_right hprod).1 hc
  norm_num at h3

theorem w183art_tqpow_U3 {p q k : ℕ} (hp : 3 ≤ p) (hq : q = 3 ∨ q = 5) (hqp : ¬ q ∣ p)
    (hk : q ^ k ∣ ordTwistedA 2 p) : (q ^ k) ^ 5 ≤ (ordTwistedA 2 p) ^ 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 3 := ⟨p - 3, by omega⟩
  set M := ordTwistedA 2 (r + 3)
  set g := Nat.gcd 3 ((r + 3) + 1)
  have hgM : g * M =
      (r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1)) := by
    simpa [M, g] using w183art_gcd_mul_ordTwistedA_two (p := r + 3)
  have hgdvd : g ∣ 3 := by simpa [g] using Nat.gcd_dvd_left 3 ((r + 3) + 1)
  have hg13 : g = 1 ∨ g = 3 := (Nat.dvd_prime Nat.prime_three).1 hgdvd
  have hgle : g ≤ 3 := by rcases hg13 with h | h <;> omega
  have hfac : (r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1)) =
      (r + 3) ^ 3 * (((r + 2) * (r + 4) ^ 2) * (r ^ 2 + 5 * r + 7)) := by
    have e1 : (r + 3) ^ 2 - 1 = (r + 2) * (r + 4) := by
      apply Nat.sub_eq_of_eq_add
      ring
    have e2 : (r + 3) ^ 3 + 1 = (r + 4) * (r ^ 2 + 5 * r + 7) := by ring
    rw [e1, e2]
    ring
  have hqprime : q.Prime := by rcases hq with rfl | rfl <;> norm_num
  have hqkN : q ^ k ∣
      (r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1)) := by
    rw [← hgM]
    rcases hg13 with hg1 | hg3
    · rw [hg1, one_mul]
      exact hk
    · rw [hg3]
      exact dvd_mul_of_dvd_right hk 3
  have hcopP : Nat.Coprime (q ^ k) ((r + 3) ^ 3) := by
    have hcp : Nat.Coprime q (r + 3) := (Nat.Prime.coprime_iff_not_dvd hqprime).2 hqp
    exact Nat.Coprime.pow_left k (Nat.Coprime.pow_right 3 hcp)
  have hqkABC : q ^ k ∣ ((r + 2) * (r + 4) ^ 2) * (r ^ 2 + 5 * r + 7) := by
    have hbig : q ^ k ∣
        (r + 3) ^ 3 * (((r + 2) * (r + 4) ^ 2) * (r ^ 2 + 5 * r + 7)) := by
      rw [← hfac]
      exact hqkN
    exact hcopP.dvd_of_dvd_mul_left hbig
  have hAle : r + 2 ≤ 2 * (r + 3) ^ 2 := by nlinarith
  have hBle : (r + 4) ^ 2 ≤ 2 * (r + 3) ^ 2 := by
    have e : (r + 4) ^ 2 = (r + 3) ^ 2 + 2 * (r + 3) + 1 := by ring
    nlinarith [sq_nonneg (r + 3), Nat.zero_le (r + 3)]
  have hCle : r ^ 2 + 5 * r + 7 ≤ 2 * (r + 3) ^ 2 := by nlinarith
  have hbound5 : (r + 4) ^ 2 ≤ 2 * (r + 3) ^ 2 := hBle
  have hAstep : q ^ k ≤ 2 * (r + 3) ^ 2 := by
    rcases hq with rfl | rfl
    ·
      by_cases h3p1 : 3 ∣ (r + 3) + 1
      ·
        obtain ⟨n, hn⟩ : ∃ n, r + 3 = 3 * n + 5 := by
          obtain ⟨m, hm⟩ := h3p1
          refine ⟨m - 2, ?_⟩
          omega
        have hCeq : (r + 3) ^ 2 - (r + 3) + 1 = 3 * (3 * n ^ 2 + 9 * n + 7) := by
          have hple : r + 3 ≤ (r + 3) ^ 2 := by nlinarith
          have h1 : (r + 3) ^ 2 - (r + 3) + 1 + (r + 3) = (r + 3) ^ 2 + 1 := by omega
          have h2 : 3 * (3 * n ^ 2 + 9 * n + 7) + (r + 3) = (r + 3) ^ 2 + 1 := by
            nlinarith
          have h3 : (r + 3) ^ 2 - (r + 3) + 1 + (r + 3) =
              3 * (3 * n ^ 2 + 9 * n + 7) + (r + 3) := by rw [h1, h2]
          exact Nat.add_right_cancel h3
        have hC : r ^ 2 + 5 * r + 7 = 3 * (3 * n ^ 2 + 9 * n + 7) := by
          have e : (r + 3) ^ 2 - (r + 3) + 1 = r ^ 2 + 5 * r + 7 := by
            have h1 : (r + 3) ^ 2 - (r + 3) + 1 + (r + 3) = (r + 3) ^ 2 + 1 := by
              omega
            have h2 : r ^ 2 + 5 * r + 7 + (r + 3) = (r + 3) ^ 2 + 1 := by ring
            have h3 : (r + 3) ^ 2 - (r + 3) + 1 + (r + 3) =
                r ^ 2 + 5 * r + 7 + (r + 3) := by rw [h1, h2]
            exact Nat.add_right_cancel h3
          rw [← e]
          exact hCeq
        have hg_eq : g = 3 := by
          have h3g : 3 ∣ g := by
            rw [show g = Nat.gcd 3 ((r + 3) + 1) by rfl]
            exact Nat.dvd_gcd (dvd_refl 3) (by simpa using h3p1)
          exact Nat.dvd_antisymm hgdvd h3g
        have h3M : 3 * M =
            (r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1)) := by
          simpa [hg_eq] using hgM
        have hN3 : (r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1)) =
            3 * ((r + 3) ^ 3 * ((r + 2) * ((r + 4) ^ 2 * (3 * n ^ 2 + 9 * n + 7)))) := by
          have e1 : (r + 3) ^ 2 - 1 = (r + 2) * (r + 4) := by
            apply Nat.sub_eq_of_eq_add
            ring
          have e2 : (r + 3) ^ 3 + 1 = (r + 4) * (r ^ 2 + 5 * r + 7) := by ring
          rw [e1, e2, hC]
          ring
        have hMD : M = (r + 3) ^ 3 *
            ((r + 2) * ((r + 4) ^ 2 * (3 * n ^ 2 + 9 * n + 7))) := by
          apply Nat.mul_left_cancel (by norm_num : 0 < 3)
          rw [h3M, hN3]
        have hqkD : 3 ^ k ∣ (r + 3) ^ 3 *
            ((r + 2) * ((r + 4) ^ 2 * (3 * n ^ 2 + 9 * n + 7))) := by
          rw [← hMD]
          exact hk
        have h3p : ¬ 3 ∣ r + 3 := by simpa using hqp
        have h3pm1 : ¬ 3 ∣ r + 2 := by
          intro h
          have h2 : 3 ∣ 2 := by
            have hsub := Nat.dvd_sub (show 3 ∣ (r + 3) + 1 from h3p1) h
            simpa using hsub
          exact not_dvd_two Nat.prime_three (by norm_num) h2
        have h3C' : ¬ 3 ∣ 3 * n ^ 2 + 9 * n + 7 := by
          intro h
          have hC'e : 3 * n ^ 2 + 9 * n + 7 = 3 * (n ^ 2 + 3 * n + 2) + 1 := by ring
          rw [hC'e] at h
          have hprod : 3 ∣ 3 * (n ^ 2 + 3 * n + 2) := dvd_mul_right 3 _
          have h1 : 3 ∣ 1 := (Nat.dvd_add_right hprod).1 h
          exact Nat.prime_three.one_lt.ne' (Nat.dvd_one.mp h1)
        have hcop3p : Nat.Coprime (3 ^ k) ((r + 3) ^ 3) := by
          have hcp : Nat.Coprime 3 (r + 3) :=
            (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3p
          exact Nat.Coprime.pow_left k (Nat.Coprime.pow_right 3 hcp)
        have hcop3pm1 : Nat.Coprime (3 ^ k) (r + 2) :=
          Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3pm1)
        have hcop3C : Nat.Coprime (3 ^ k) (3 * n ^ 2 + 9 * n + 7) :=
          Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3C')
        have h1 : 3 ^ k ∣ (r + 2) * ((r + 4) ^ 2 * (3 * n ^ 2 + 9 * n + 7)) :=
          hcop3p.dvd_of_dvd_mul_left hqkD
        have h2 : 3 ^ k ∣ (r + 4) ^ 2 * (3 * n ^ 2 + 9 * n + 7) :=
          hcop3pm1.dvd_of_dvd_mul_left h1
        have h3 : 3 ^ k ∣ (r + 4) ^ 2 := hcop3C.dvd_of_dvd_mul_right h2
        exact (Nat.le_of_dvd (by positivity) h3).trans hBle
      ·
        have h3np1 : ¬ 3 ∣ r + 4 := by simpa using h3p1
        have hAB : ¬ (3 ∣ r + 2 ∧ 3 ∣ (r + 4) ^ 2) := by
          rintro ⟨ha, hb⟩
          exact w183art_not_both_dvd_A_B (by norm_num) (by norm_num) ha hb
        have hAC : ¬ (3 ∣ r + 2 ∧ 3 ∣ r ^ 2 + 5 * r + 7) := by
          rintro ⟨ha, hc⟩
          exact w183art_not_both_dvd_A_C (by norm_num) ha hc
        have hBC : ¬ (3 ∣ (r + 4) ^ 2 ∧ 3 ∣ r ^ 2 + 5 * r + 7) := by
          rintro ⟨hb, _⟩
          exact h3np1 ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow hb)
        have hdisj := prime_pow_dvd_mul3 (by norm_num : Nat.Prime 3) hAB hAC hBC hqkABC
        rcases hdisj with h | h | h
        · exact (Nat.le_of_dvd (by positivity) h).trans hAle
        · exact (Nat.le_of_dvd (by positivity) h).trans hBle
        · exact (Nat.le_of_dvd (by positivity) h).trans hCle
    ·
      have hAB : ¬ (5 ∣ r + 2 ∧ 5 ∣ (r + 4) ^ 2) := by
        rintro ⟨ha, hb⟩
        exact w183art_not_both_dvd_A_B (by norm_num) (by norm_num) ha hb
      have hAC : ¬ (5 ∣ r + 2 ∧ 5 ∣ r ^ 2 + 5 * r + 7) := by
        rintro ⟨ha, hc⟩
        exact w183art_not_both_dvd_A_C (by norm_num) ha hc
      have hBC : ¬ (5 ∣ (r + 4) ^ 2 ∧ 5 ∣ r ^ 2 + 5 * r + 7) :=
        fun h => w183art_not_both_dvd_B_C_of_five r h.1 h.2
      have hdisj := prime_pow_dvd_mul3 (by norm_num : Nat.Prime 5) hAB hAC hBC hqkABC
      rcases hdisj with h | h | h
      · exact (Nat.le_of_dvd (by positivity) h).trans hAle
      · exact (Nat.le_of_dvd (by positivity) h).trans hBle
      · exact (Nat.le_of_dvd (by positivity) h).trans hCle
  have hNle : (r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1)) ≤ 3 * M := by
    rw [← hgM]
    exact Nat.mul_le_mul_right M hgle
  have hkey : 3 * (r + 3) ^ 8 ≤
      4 * ((r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1))) := by
    have e1 : (r + 3) ^ 2 - 1 = r ^ 2 + 6 * r + 8 := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e1]
    have e : 4 * ((r + 3) ^ 3 * ((r ^ 2 + 6 * r + 8) * ((r + 3) ^ 3 + 1))) =
        3 * (r + 3) ^ 8 + (r ^ 8 + 24 * r ^ 7 + 248 * r ^ 6 + 1444 * r ^ 5 +
          5190 * r ^ 4 + 11804 * r ^ 3 + 16596 * r ^ 2 + 13176 * r + 4509) := by
      ring
    rw [e]
    have hnn : 0 ≤ r ^ 8 + 24 * r ^ 7 + 248 * r ^ 6 + 1444 * r ^ 5 +
        5190 * r ^ 4 + 11804 * r ^ 3 + 16596 * r ^ 2 + 13176 * r + 4509 := by positivity
    omega
  have hp8 : (r + 3) ^ 8 ≤ 4 * M := by
    have h1 : 3 * (r + 3) ^ 8 ≤ 12 * M := by
      calc 3 * (r + 3) ^ 8 ≤
            4 * ((r + 3) ^ 3 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 3 + 1))) := hkey
        _ ≤ 4 * (3 * M) := Nat.mul_le_mul_left 4 hNle
        _ = 12 * M := by ring
    omega
  have hp16 : (r + 3) ^ 16 ≤ 16 * M ^ 2 := by
    have h2 := Nat.pow_le_pow_left hp8 2
    nlinarith
  have h512 : 512 ≤ (r + 3) ^ 6 := by
    have h3 : 3 ^ 6 ≤ (r + 3) ^ 6 := Nat.pow_le_pow_left (by omega : 3 ≤ r + 3) 6
    omega
  have hBstep : 32 * (r + 3) ^ 10 ≤ M ^ 2 := by
    have h1 : 512 * (r + 3) ^ 10 ≤ (r + 3) ^ 16 := by
      calc 512 * (r + 3) ^ 10 ≤ (r + 3) ^ 6 * (r + 3) ^ 10 :=
            Nat.mul_le_mul_right ((r + 3) ^ 10) h512
        _ = (r + 3) ^ 16 := by ring
    have h2 : 512 * (r + 3) ^ 10 ≤ 16 * M ^ 2 := h1.trans hp16
    nlinarith
  have h5 : (q ^ k) ^ 5 ≤ (2 * (r + 3) ^ 2) ^ 5 := Nat.pow_le_pow_left hAstep 5
  calc (q ^ k) ^ 5 ≤ (2 * (r + 3) ^ 2) ^ 5 := h5
    _ = 32 * (r + 3) ^ 10 := by ring
    _ ≤ M ^ 2 := hBstep

end CFSG.LocalAnalysis.WeakClosure81
