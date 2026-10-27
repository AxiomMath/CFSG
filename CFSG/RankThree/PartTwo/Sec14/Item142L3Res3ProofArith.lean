module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofDickson
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofTorus
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.Timmesfeld.Orders.Bang
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open CFSG.RankThree.PartTwo.Sec14.L3PGLU (mU mU_dvd)

theorem nine_mul_mU_dvd {q : ℕ} (h9 : q % 9 = 8) : 9 * mU q ∣ q + 1 := by
  have hn : q + 1 ≠ 0 := Nat.succ_ne_zero q
  have h1 : 2 ≤ (q + 1).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn).mp (by norm_num; omega)
  have h3 : 3 ^ (q + 1).factorization 3 * mU q = q + 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (q + 1) 3
  rw [← h3]
  exact Nat.mul_dvd_mul_right ((show 9 = 3 ^ 2 by norm_num) ▸ Nat.pow_dvd_pow 3 (by omega)) _

theorem dvd_mU_of_prime {q ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hℓq : ℓ ∣ q + 1) :
    ℓ ∣ mU q := by
  have h3 : 3 ^ (q + 1).factorization 3 * mU q = q + 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (q + 1) 3
  rw [← h3] at hℓq
  have hcop : Nat.Coprime ℓ (3 ^ (q + 1).factorization 3) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ Nat.prime_three).mpr hℓ3)
  exact hcop.dvd_of_dvd_mul_left hℓq

theorem three_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : 3 ∣ p ^ 2 - 1 := by
  have h0 : p % 3 ≠ 0 := fun h0 =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)).symm
  have h12 : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have h1 : p ^ 2 % 3 = 1 := by
    rcases h12 with h | h <;> simp [Nat.pow_mod, h]
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  exact Nat.dvd_of_mod_eq_zero (by omega)

theorem mU_facts {p f : ℕ} (hp : p.Prime) (h9 : p ^ f % 9 = 8) (h8 : p ^ f ≠ 8) :
    2 ≤ mU (p ^ f) ∧ SubfieldFree p f (3 * mU (p ^ f)) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    norm_num at h9
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 hf0
    omega
  have hm0 : 0 < mU (p ^ f) :=
    Nat.pos_of_ne_zero fun h0 => by
      have := mU_dvd (p ^ f)
      rw [h0, zero_dvd_iff] at this
      omega
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · have hf : f = 1 := by omega
    subst hf
    have hp2 : p ≠ 2 := by
      rintro rfl
      norm_num at h9
    have h2q : 2 ∣ p ^ 1 + 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · rw [pow_one]
        omega
    have h2m := dvd_mU_of_prime Nat.prime_two (by norm_num) h2q
    exact ⟨Nat.le_of_dvd hm0 h2m, 3, Nat.prime_three, dvd_mul_right 3 _, fun j hj hj1 => by
      omega⟩
  · obtain ⟨ℓ, hℓ, hℓdvd, hℓprim⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ p ^ (2 * f) - 1 ∧
        ∀ k : ℕ, 0 < k → k < 2 * f → ¬ ℓ ∣ p ^ k - 1 := by
      rcases hp.eq_two_or_odd' with rfl | hodd
      · have hf3 : f ≠ 3 := by
          rintro rfl
          norm_num at h8
        exact CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * f) (by omega)
          (by omega)
      · have hp3' : 3 ≤ p := by
          obtain ⟨k, hk⟩ := hodd
          have := hp.two_le
          omega
        exact CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3' (by omega)
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    have hsplit : p ^ (2 * f) - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      have e : p ^ (2 * f) = p ^ f * p ^ f := by rw [two_mul, pow_add]
      rw [e]
      zify [hq1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega) :
        p ^ f * p ^ f ≠ 0)]
      ring
    have hℓq1 : ¬ ℓ ∣ p ^ f - 1 := hℓprim f (by omega) (by omega)
    have hℓq : ℓ ∣ p ^ f + 1 :=
      ((Nat.Prime.dvd_mul hℓ).1 (hsplit ▸ hℓdvd)).resolve_left hℓq1
    have hℓ3 : ℓ ≠ 3 := by
      rintro rfl
      exact hℓprim 2 (by norm_num) (by omega) (three_dvd_sq_sub_one hp hp3)
    have hℓm := dvd_mU_of_prime hℓ hℓ3 hℓq
    refine ⟨le_trans hℓ.two_le (Nat.le_of_dvd hm0 hℓm), ℓ, hℓ, dvd_mul_of_dvd_right hℓm 3,
      fun j hj hjf => hℓprim (2 * j) (by omega) (by omega)⟩

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
