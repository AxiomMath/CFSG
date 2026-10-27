module

public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinForms
import CFSG.GH74.GLS.Stage2.Final.ModelArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.GH74.GLS.Stage2.Final.ModelArith

theorem w183art_tqpow_L2 {x q k : ℕ} (hx : 10 ≤ x) (hxodd : Odd x) (hq : q = 3 ∨ q = 5)
    (hqx : ¬ q ∣ x) (hk : q ^ k ∣ ordA 1 x) : (q ^ k) ^ 5 ≤ (ordA 1 x) ^ 2 := by
  have hqprime : q.Prime := by
    rcases hq with hq | hq
    · rw [hq]; exact Nat.prime_three
    · rw [hq]; exact Nat.prime_five
  have hq2 : q ≠ 2 := by
    rcases hq with hq | hq <;> (rw [hq]; norm_num)
  have hnd2 : ¬ q ∣ 2 := not_dvd_two hqprime hq2
  obtain ⟨m, hm⟩ := hxodd
  have hxm : x - 1 = 2 * m := by omega
  have h2dvd : 2 ∣ x - 1 := ⟨m, hxm⟩
  have hgcd : Nat.gcd 2 (x - 1) = 2 := Nat.gcd_eq_left h2dvd
  have hx2 : x ^ 2 - 1 = (x - 1) * (x + 1) := by
    rw [hxm]
    apply Nat.sub_eq_of_eq_add
    rw [hm]
    ring
  have h2M : 2 * ordA 1 x = x * ((x - 1) * (x + 1)) := by
    have hforms := w183art_gcd_mul_ordA_one (show 1 ≤ x by omega)
    rw [hgcd, hx2] at hforms
    exact hforms
  have hkprod : q ^ k ∣ x * ((x - 1) * (x + 1)) := by
    rw [← h2M]
    exact hk.trans (Nat.dvd_mul_left (ordA 1 x) 2)
  have hcopx : Nat.Coprime (q ^ k) x :=
    Nat.Coprime.pow_left k ((hqprime.coprime_iff_not_dvd).2 hqx)
  have hkfac : q ^ k ∣ (x - 1) * (x + 1) := hcopx.dvd_of_dvd_mul_left hkprod
  have hnotboth : ¬ (q ∣ x - 1 ∧ q ∣ x + 1) := by
    rintro ⟨h1, h2⟩
    have hsub : q ∣ 2 := by
      have h := Nat.dvd_sub h2 h1
      have e : (x + 1) - (x - 1) = 2 := by omega
      rwa [e] at h
    exact hnd2 hsub
  have hle : q ^ k ≤ x + 1 := by
    have hcase : q ^ k ∣ x - 1 ∨ q ^ k ∣ x + 1 := by
      by_cases h1 : q ∣ x - 1
      · left
        have h2 : ¬ q ∣ x + 1 := fun h2 => hnotboth ⟨h1, h2⟩
        have hcop : Nat.Coprime (q ^ k) (x + 1) :=
          Nat.Coprime.pow_left k ((hqprime.coprime_iff_not_dvd).2 h2)
        exact Nat.Coprime.dvd_of_dvd_mul_right (k := q ^ k) (m := x - 1) (n := x + 1)
          hcop hkfac
      · right
        have hcop : Nat.Coprime (q ^ k) (x - 1) :=
          Nat.Coprime.pow_left k ((hqprime.coprime_iff_not_dvd).2 h1)
        exact Nat.Coprime.dvd_of_dvd_mul_left (k := q ^ k) (m := x - 1) (n := x + 1)
          hcop hkfac
    rcases hcase with h | h
    · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
    · exact Nat.le_of_dvd (by omega) h
  have hpow : (x + 1) ^ 5 ≤ (ordA 1 x) ^ 2 := by
    have hstep : 4 * (x + 1) ^ 5 ≤ (2 * ordA 1 x) ^ 2 := by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 10 := ⟨x - 10, by omega⟩
      have hsub : (y + 10 - 1) * (y + 10 + 1) = y ^ 2 + 20 * y + 99 := by
        have e : y + 10 - 1 = y + 9 := by omega
        rw [e]; ring
      have h2My : 2 * ordA 1 (y + 10) =
          (y + 10) * (y ^ 2 + 20 * y + 99) := by
        rw [h2M, hsub]
      rw [h2My]
      have hkey : ((y + 10) * (y ^ 2 + 20 * y + 99)) ^ 2 =
          4 * (y + 11) ^ 5 + (y ^ 6 + 56 * y ^ 5 + 1278 * y ^ 4 + 15080 * y ^ 3
            + 95561 * y ^ 2 + 299200 * y + 335896) := by ring
      rw [hkey]
      have hy : y + 10 + 1 = y + 11 := by omega
      rw [hy]
      exact Nat.le_add_right _ _
    have h4 : 4 * (x + 1) ^ 5 ≤ 4 * (ordA 1 x) ^ 2 := by
      calc 4 * (x + 1) ^ 5 ≤ (2 * ordA 1 x) ^ 2 := hstep
        _ = 4 * (ordA 1 x) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  calc (q ^ k) ^ 5 ≤ (x + 1) ^ 5 := Nat.pow_le_pow_left hle 5
    _ ≤ (ordA 1 x) ^ 2 := hpow

end CFSG.LocalAnalysis.WeakClosure81
