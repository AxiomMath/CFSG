module

public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinForms
import CFSG.GH74.GLS.Stage2.Final.ModelArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.GH74.GLS.Stage2.Final.ModelArith

private lemma w183art_tqpow_L3_easy {q k a : ℕ} (ha : 1 ≤ a) (hq : q = 3 ∨ q = 5)
    (hbad : q = 3 → ¬ 3 ∣ a)
    (hcop : Nat.Coprime (q ^ k) ((a + 1) ^ 3))
    (hdiv : q ^ k ∣ (a + 1) ^ 3 * (a ^ 2 * ((a + 2) * (a ^ 2 + 3 * a + 3)))) :
    q ^ k ≤ 2 * (a + 1) ^ 2 := by
  have hqprime : q.Prime := by
    rcases hq with hq | hq
    · rw [hq]; exact Nat.prime_three
    · rw [hq]; exact Nat.prime_five
  have hq2 : q ≠ 2 := by
    rcases hq with hq | hq <;> (rw [hq]; norm_num)
  have hdiv' : q ^ k ∣ (a ^ 2 * (a + 2)) * (a ^ 2 + 3 * a + 3) := by
    have h := hcop.dvd_of_dvd_mul_left hdiv
    rwa [← mul_assoc] at h
  have ha2a : ¬ (q ∣ a ∧ q ∣ a + 2) := by
    rintro ⟨h1, h2⟩
    have h2dvd : q ∣ 2 := by
      have hsub := Nat.dvd_sub h2 h1
      have e : (a + 2) - a = 2 := by omega
      rwa [e] at hsub
    exact (not_dvd_two hqprime hq2) h2dvd
  have hac : ¬ (q ∣ a ∧ q ∣ a ^ 2 + 3 * a + 3) := by
    rintro ⟨h1, h2⟩
    have h3dvd : q ∣ 3 := by
      have hsub := Nat.dvd_sub h2 (Dvd.dvd.mul_right h1 (a + 3))
      have e : a ^ 2 + 3 * a + 3 - a * (a + 3) = 3 := by
        apply Nat.sub_eq_of_eq_add; ring
      rwa [e] at hsub
    have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1 h3dvd
    exact hbad hq3 (hq3 ▸ h1)
  have hbc : ¬ (q ∣ a + 2 ∧ q ∣ a ^ 2 + 3 * a + 3) := by
    rintro ⟨h1, h2⟩
    have h1dvd : q ∣ 1 := by
      have hsub := Nat.dvd_sub h2 (Dvd.dvd.mul_right h1 (a + 1))
      have e : a ^ 2 + 3 * a + 3 - (a + 2) * (a + 1) = 1 := by
        apply Nat.sub_eq_of_eq_add; ring
      rwa [e] at hsub
    exact hqprime.ne_one (Nat.dvd_one.1 h1dvd)
  have hab' : ¬ (q ∣ a ^ 2 ∧ q ∣ a + 2) := by
    rintro ⟨h1, h2⟩
    exact ha2a ⟨hqprime.dvd_of_dvd_pow h1, h2⟩
  have hac' : ¬ (q ∣ a ^ 2 ∧ q ∣ a ^ 2 + 3 * a + 3) := by
    rintro ⟨h1, h2⟩
    exact hac ⟨hqprime.dvd_of_dvd_pow h1, h2⟩
  rcases prime_pow_dvd_mul3 hqprime hab' hac' hbc hdiv' with h | h | h
  · have hle := Nat.le_of_dvd (by nlinarith) h
    nlinarith
  · have hle := Nat.le_of_dvd (by nlinarith) h
    nlinarith
  · have hle := Nat.le_of_dvd (by nlinarith) h
    nlinarith

private lemma w183art_tqpow_L3_three {k a : ℕ} (ha : 1 ≤ a) (h3a : 3 ∣ a)
    (hN : Nat.gcd 3 a * ordA 2 (a + 1) =
      (a + 1) ^ 3 * (a ^ 2 * ((a + 2) * (a ^ 2 + 3 * a + 3))))
    (hk : 3 ^ k ∣ ordA 2 (a + 1)) :
    3 ^ k ≤ 2 * (a + 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 3 * m := h3a
  have hm : 1 ≤ m := by omega
  have hg : Nat.gcd 3 (3 * m) = 3 := Nat.gcd_eq_left ⟨m, by ring⟩
  rw [hg] at hN
  have h1 : 3 ^ (k + 1) ∣ 3 * ordA 2 (3 * m + 1) := by
    have h := Nat.mul_dvd_mul_left 3 hk
    simpa [pow_succ, mul_comm] using h
  rw [hN] at h1
  have hkey : (3 * m + 1) ^ 3 *
        ((3 * m) ^ 2 * ((3 * m + 2) * ((3 * m) ^ 2 + 3 * (3 * m) + 3))) =
      ((3 * m + 1) ^ 3 * ((3 * m + 2) * (3 * m ^ 2 + 3 * m + 1))) * (27 * m ^ 2) := by
    ring
  rw [hkey] at h1
  have h3p : Nat.Prime 3 := Nat.prime_three
  have hc1b : Nat.Coprime 3 (3 * m + 1) :=
    (h3p.coprime_iff_not_dvd).2 (by
      intro h
      obtain ⟨c, hc⟩ := h
      omega)
  have hc1 : Nat.Coprime (3 ^ (k + 1)) ((3 * m + 1) ^ 3) :=
    (hc1b.pow_left (k + 1)).pow_right 3
  have hc2 : Nat.Coprime (3 ^ (k + 1)) (3 * m + 2) :=
    ((h3p.coprime_iff_not_dvd).2 (by
      intro h
      obtain ⟨c, hc⟩ := h
      omega)).pow_left (k + 1)
  have hc3 : Nat.Coprime (3 ^ (k + 1)) (3 * m ^ 2 + 3 * m + 1) :=
    ((h3p.coprime_iff_not_dvd).2 (by
      intro h
      obtain ⟨c, hc⟩ := h
      omega)).pow_left (k + 1)
  have hcP : Nat.Coprime (3 ^ (k + 1))
      ((3 * m + 1) ^ 3 * ((3 * m + 2) * (3 * m ^ 2 + 3 * m + 1))) :=
    hc1.mul_right (hc2.mul_right hc3)
  have h3dvd : 3 ^ (k + 1) ∣ 27 * m ^ 2 := hcP.dvd_of_dvd_mul_left h1
  have hle : 3 ^ (k + 1) ≤ 27 * m ^ 2 := Nat.le_of_dvd (by nlinarith [hm]) h3dvd
  have hle2 : 3 * 3 ^ k ≤ 27 * m ^ 2 := by simpa [pow_succ, mul_comm] using hle
  have hle3 : 3 ^ k ≤ 9 * m ^ 2 := by omega
  have hfin : 9 * m ^ 2 ≤ 2 * (3 * m + 1) ^ 2 := by nlinarith [hm]
  omega

private lemma w183art_tqpow_L3_size {p : ℕ} (hp : 3 ≤ p) :
    32 * p ^ 10 ≤ (ordA 2 p) ^ 2 := by
  obtain ⟨y, rfl⟩ : ∃ y, p = y + 3 := ⟨p - 3, by omega⟩
  have hforms := w183art_gcd_mul_ordA_two (show 1 ≤ y + 3 by omega)
  have hgle : Nat.gcd 3 ((y + 3) - 1) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 ((y + 3) - 1))
  have hNM : (y + 3) ^ 3 * (((y + 3) ^ 2 - 1) * ((y + 3) ^ 3 - 1)) ≤
      3 * ordA 2 (y + 3) := by
    rw [← hforms]
    exact Nat.mul_le_mul_right _ hgle
  have hsize : 3 * (y + 3) ^ 8 ≤
      4 * ((y + 3) ^ 3 * (((y + 3) ^ 2 - 1) * ((y + 3) ^ 3 - 1))) := by
    have e2 : (y + 3) ^ 2 - 1 = y ^ 2 + 6 * y + 8 := by
      apply Nat.sub_eq_of_eq_add; ring
    have e3 : (y + 3) ^ 3 - 1 = y ^ 3 + 9 * y ^ 2 + 27 * y + 26 := by
      apply Nat.sub_eq_of_eq_add; ring
    have key : 4 * ((y + 3) ^ 3 *
          ((y ^ 2 + 6 * y + 8) * (y ^ 3 + 9 * y ^ 2 + 27 * y + 26))) =
        3 * (y + 3) ^ 8 + (y ^ 8 + 24 * y ^ 7 + 248 * y ^ 6 + 1436 * y ^ 5 + 5070 * y ^ 4
          + 11092 * y ^ 3 + 14508 * y ^ 2 + 10152 * y + 2781) := by ring
    rw [e2, e3, key]
    exact Nat.le_add_right _ _
  have hp8 : (y + 3) ^ 8 ≤ 4 * ordA 2 (y + 3) := by nlinarith [hsize, hNM]
  have h16 : (y + 3) ^ 16 ≤ 16 * (ordA 2 (y + 3)) ^ 2 := by
    calc (y + 3) ^ 16 = ((y + 3) ^ 8) ^ 2 := by ring
      _ ≤ (4 * ordA 2 (y + 3)) ^ 2 := Nat.pow_le_pow_left hp8 2
      _ = 16 * (ordA 2 (y + 3)) ^ 2 := by ring
  have h512 : 512 * (y + 3) ^ 10 ≤ (y + 3) ^ 16 := by
    have h6 : 512 ≤ (y + 3) ^ 6 := by
      calc 512 ≤ 3 ^ 6 := by norm_num
        _ ≤ (y + 3) ^ 6 := Nat.pow_le_pow_left (by omega : 3 ≤ y + 3) 6
    have hmul := Nat.mul_le_mul_right ((y + 3) ^ 10) h6
    simpa [← pow_add] using hmul
  have hfin : 512 * (y + 3) ^ 10 ≤ 16 * (ordA 2 (y + 3)) ^ 2 := le_trans h512 h16
  omega

theorem w183art_tqpow_L3 {p q k : ℕ} (hp : 3 ≤ p) (hq : q = 3 ∨ q = 5) (hqp : ¬ q ∣ p)
    (hk : q ^ k ∣ ordA 2 p) : (q ^ k) ^ 5 ≤ (ordA 2 p) ^ 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  have ha : 1 ≤ a := by omega
  have hforms := w183art_gcd_mul_ordA_two (show 1 ≤ a + 1 by omega)
  have hN : Nat.gcd 3 a * ordA 2 (a + 1) =
      (a + 1) ^ 3 * (a ^ 2 * ((a + 2) * (a ^ 2 + 3 * a + 3))) := by
    have h1 : (a + 1) - 1 = a := by omega
    rw [h1] at hforms
    have e2 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
      apply Nat.sub_eq_of_eq_add; ring
    have e3 : (a + 1) ^ 3 - 1 = a * (a ^ 2 + 3 * a + 3) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e2, e3] at hforms
    rw [hforms]; ring
  have hMN : ordA 2 (a + 1) ∣
      (a + 1) ^ 3 * (a ^ 2 * ((a + 2) * (a ^ 2 + 3 * a + 3))) :=
    ⟨Nat.gcd 3 a, hN.symm.trans (mul_comm (Nat.gcd 3 a) (ordA 2 (a + 1)))⟩
  have hkN : q ^ k ∣ (a + 1) ^ 3 * (a ^ 2 * ((a + 2) * (a ^ 2 + 3 * a + 3))) :=
    hk.trans hMN
  have hqprime : q.Prime := by
    rcases hq with hq | hq
    · rw [hq]; exact Nat.prime_three
    · rw [hq]; exact Nat.prime_five
  have hcop : Nat.Coprime (q ^ k) ((a + 1) ^ 3) :=
    (((hqprime.coprime_iff_not_dvd).2 hqp).pow_left k).pow_right 3
  have hA : q ^ k ≤ 2 * (a + 1) ^ 2 := by
    by_cases hq3 : q = 3
    · subst hq3
      by_cases h3a : 3 ∣ a
      · exact w183art_tqpow_L3_three ha h3a hN hk
      · exact w183art_tqpow_L3_easy ha (Or.inl rfl) (fun _ => h3a) hcop hkN
    · exact w183art_tqpow_L3_easy ha hq (fun h => by omega) hcop hkN
  have hB : 32 * (a + 1) ^ 10 ≤ (ordA 2 (a + 1)) ^ 2 := w183art_tqpow_L3_size (by omega)
  calc (q ^ k) ^ 5 ≤ (2 * (a + 1) ^ 2) ^ 5 := Nat.pow_le_pow_left hA 5
    _ = 32 * (a + 1) ^ 10 := by ring
    _ ≤ (ordA 2 (a + 1)) ^ 2 := hB

end CFSG.LocalAnalysis.WeakClosure81
