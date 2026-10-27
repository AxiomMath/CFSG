module

public import CFSG.Open.Defs
import CFSG.GH74.GLS.Stage2.Final.ModelArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.GH74.GLS.Stage2.Final.ModelArith

theorem w183art_tqpow_Sp4 {p q k : ℕ} (hp : 3 ≤ p) (hpodd : Odd p) (hq : q = 3 ∨ q = 5)
    (hqp : ¬ q ∣ p) (hk : q ^ k ∣ ordBC 2 p) : (q ^ k) ^ 5 ≤ (ordBC 2 p) ^ 2 := by
  have hqprime : q.Prime := by
    rcases hq with hq | hq
    · rw [hq]; exact Nat.prime_three
    · rw [hq]; exact Nat.prime_five
  have hq2 : q ≠ 2 := by
    rcases hq with hq | hq <;> (rw [hq]; norm_num)
  have hnot2 : ¬ q ∣ 2 := not_dvd_two hqprime hq2
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have hN : 2 * ordBC 2 (r + 1) =
      (r + 1) ^ 4 * (((r + 1) ^ 2 - 1) * ((r + 1) ^ 4 - 1)) := two_mul_ordBC_two hpodd
  have hkN : q ^ k ∣ (r + 1) ^ 4 * (((r + 1) ^ 2 - 1) * ((r + 1) ^ 4 - 1)) := by
    rw [← hN]
    exact dvd_mul_of_dvd_right hk 2
  have hcop : Nat.Coprime (q ^ k) ((r + 1) ^ 4) :=
    (((hqprime.coprime_iff_not_dvd).2 hqp).pow_left k).pow_right 4
  have hdiv : q ^ k ∣ ((r + 1) ^ 2 - 1) * ((r + 1) ^ 4 - 1) :=
    hcop.dvd_of_dvd_mul_left hkN
  have e : ((r + 1) ^ 2 - 1) * ((r + 1) ^ 4 - 1) =
      r ^ 2 * (r + 2) ^ 2 * ((r + 1) ^ 2 + 1) := by
    have e1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : (r + 1) ^ 4 - 1 = r * (r + 2) * ((r + 1) ^ 2 + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2]; ring
  rw [e] at hdiv
  have hab : ¬ (q ∣ r ^ 2 ∧ q ∣ (r + 2) ^ 2) := by
    rintro ⟨h1, h2⟩
    have h1' := hqprime.dvd_of_dvd_pow h1
    have h2' := hqprime.dvd_of_dvd_pow h2
    have hsub : q ∣ 2 := by
      have h := Nat.dvd_sub h2' h1'
      rwa [show (r + 2) - r = 2 by omega] at h
    exact hnot2 hsub
  have hac : ¬ (q ∣ r ^ 2 ∧ q ∣ (r + 1) ^ 2 + 1) := by
    rintro ⟨h1, h2⟩
    have h1' := hqprime.dvd_of_dvd_pow h1
    have hsub : q ∣ 2 := by
      have h2' : q ∣ r * (r + 2) + 2 := by
        rwa [show (r + 1) ^ 2 + 1 = r * (r + 2) + 2 by ring] at h2
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right h1' (r + 2))).1 h2'
    exact hnot2 hsub
  have hbc : ¬ (q ∣ (r + 2) ^ 2 ∧ q ∣ (r + 1) ^ 2 + 1) := by
    rintro ⟨h1, h2⟩
    have h1' := hqprime.dvd_of_dvd_pow h1
    have hsub : q ∣ 2 := by
      have h2' : q ∣ (r + 2) * r + 2 := by
        rwa [show (r + 1) ^ 2 + 1 = (r + 2) * r + 2 by ring] at h2
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right h1' r)).1 h2'
    exact hnot2 hsub
  have key : q ^ k ∣ r ^ 2 ∨ q ^ k ∣ (r + 2) ^ 2 ∨ q ^ k ∣ (r + 1) ^ 2 + 1 :=
    prime_pow_dvd_mul3 hqprime hab hac hbc hdiv
  have hA : q ^ k ≤ (r + 2) ^ 2 := by
    rcases key with h | h | h
    · calc q ^ k ≤ r ^ 2 := Nat.le_of_dvd (pow_pos (by omega) 2) h
        _ ≤ (r + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    · exact Nat.le_of_dvd (pow_pos (by omega) 2) h
    · calc q ^ k ≤ (r + 1) ^ 2 + 1 := Nat.le_of_dvd (by positivity) h
        _ ≤ (r + 2) ^ 2 := by nlinarith
  have hsize : (r + 2) ^ 5 ≤ ordBC 2 (r + 1) := by
    have h := size_ineq (show 3 ≤ r + 1 by omega)
    rw [← two_mul_ordBC_two hpodd] at h
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  calc (q ^ k) ^ 5 ≤ ((r + 2) ^ 2) ^ 5 := Nat.pow_le_pow_left hA 5
    _ = ((r + 2) ^ 5) ^ 2 := by ring
    _ ≤ (ordBC 2 (r + 1)) ^ 2 := Nat.pow_le_pow_left hsize 2

end CFSG.LocalAnalysis.WeakClosure81
