module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofLinDickson
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

theorem nine_mul_mL_dvd {q : ℕ} (hq : 2 ≤ q) (h9 : q % 9 = 1) :
    9 * ordCompl[3] (q - 1) ∣ q - 1 := by
  have hn : q - 1 ≠ 0 := by omega
  have h9' : 3 ^ 2 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by norm_num; omega)
  have h1 : 2 ≤ (q - 1).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn).mp h9'
  have h3 : 3 ^ (q - 1).factorization 3 * ordCompl[3] (q - 1) = q - 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (q - 1) 3
  conv_rhs => rw [← h3]
  exact Nat.mul_dvd_mul_right ((show 9 = 3 ^ 2 by norm_num) ▸ Nat.pow_dvd_pow 3 (by omega)) _

theorem dvd_mL_of_prime {n ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hℓn : ℓ ∣ n) :
    ℓ ∣ ordCompl[3] n := by
  have h3 : 3 ^ n.factorization 3 * ordCompl[3] n = n := Nat.ordProj_mul_ordCompl_eq_self n 3
  rw [← h3] at hℓn
  have hcop : Nat.Coprime ℓ (3 ^ n.factorization 3) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ Nat.prime_three).mpr hℓ3)
  exact hcop.dvd_of_dvd_mul_left hℓn

theorem dvd_pow_sub_one_iff_zmod {p ℓ k : ℕ} (hp : 0 < p) :
    ℓ ∣ p ^ k - 1 ↔ (p : ZMod ℓ) ^ k = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hp), Nat.cast_pow,
    Nat.cast_one, sub_eq_zero]

theorem ordProj_three_le {s : ℕ} (hs : 1 ≤ s) :
    3 ^ (s * s - 1).factorization 3 ≤ s + 1 := by
  set P := 3 ^ (s * s - 1).factorization 3 with hP
  have hPd : P ∣ s * s - 1 := Nat.ordProj_dvd (s * s - 1) 3
  have he : s * s - 1 = (s - 1) * (s + 1) := by
    zify [hs, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega) : s * s ≠ 0)]
    ring
  rw [he] at hPd
  by_cases h3 : 3 ∣ s + 1
  · have h3' : ¬ 3 ∣ s - 1 := by omega
    have hcop : Nat.Coprime P (s - 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
    have := hcop.dvd_of_dvd_mul_left hPd
    exact Nat.le_of_dvd (by omega) this
  · have hcop : Nat.Coprime P (s + 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    have := hcop.dvd_of_dvd_mul_right hPd
    rcases Nat.eq_zero_or_pos (s - 1) with h0 | h0
    · have hs1 : s = 1 := by omega
      subst hs1
      simp [hP]
    · exact (Nat.le_of_dvd h0 this).trans (by omega)

theorem mL_facts {p f : ℕ} (hp : p.Prime) (hf0 : f ≠ 0) (h9 : p ^ f % 9 = 1) :
    2 ≤ ordCompl[3] (p ^ f - 1) ∧ SubfieldOK p f (3 * ordCompl[3] (p ^ f - 1)) := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 hf0
    omega
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow hf0 p)
  set q := p ^ f with hq
  set m := ordCompl[3] (q - 1) with hm
  have hqm : 3 ^ (q - 1).factorization 3 * m = q - 1 := Nat.ordProj_mul_ordCompl_eq_self (q - 1) 3
  have hm0 : 0 < m := Nat.ordCompl_pos 3 (by omega)
  have h7 : q = 64 → 7 ∣ m := fun h64 =>
    dvd_mL_of_prime (by norm_num) (by norm_num) (by rw [h64]; norm_num)
  have hprim : 3 ≤ f → q ≠ 64 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ p ^ f - 1 ∧
      ∀ k : ℕ, 0 < k → k < f → ¬ ℓ ∣ p ^ k - 1 := by
    intro hf3 h64
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have hf6 : f ≠ 6 := by
        rintro rfl
        exact h64 (by norm_num [hq])
      exact CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one f (by omega) hf6
    · have hp3' : 3 ≤ p := by
        obtain ⟨k, hk⟩ := hodd
        have := hp.two_le
        omega
      exact CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3' hf3
  have hord : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ p ^ f - 1 → (∀ k : ℕ, 0 < k → k < f → ¬ ℓ ∣ p ^ k - 1) →
      ∀ k : ℕ, ℓ ∣ p ^ k - 1 → f ∣ k := by
    intro ℓ hℓ hℓf hℓk k hk
    have := Fact.mk hℓ
    have hof : orderOf (p : ZMod ℓ) = f := by
      rw [orderOf_eq_iff (Nat.pos_of_ne_zero hf0)]
      refine ⟨(dvd_pow_sub_one_iff_zmod hp.pos).mp hℓf, fun j hj hj0 h1 => ?_⟩
      exact hℓk j hj0 hj ((dvd_pow_sub_one_iff_zmod hp.pos).mpr h1)
    rw [← hof]
    exact orderOf_dvd_of_pow_eq_one ((dvd_pow_sub_one_iff_zmod hp.pos).mp hk)
  have hm2 : 2 ≤ m := by
    rcases hp.eq_two_or_odd' with hp2 | hodd
    · subst hp2
      by_cases h64 : q = 64
      · exact le_trans (by norm_num) (Nat.le_of_dvd hm0 (h7 h64))
      · have hf3 : 3 ≤ f := by
          by_contra hlt
          interval_cases f <;> revert h9 hf0 <;> norm_num [hq]
        obtain ⟨ℓ, hℓ, hℓf, hℓk⟩ := hprim hf3 h64
        have hℓ3 : ℓ ≠ 3 := by
          rintro rfl
          exact hℓk 2 (by norm_num) (by omega) (by norm_num)
        exact le_trans hℓ.two_le (Nat.le_of_dvd hm0 (dvd_mL_of_prime hℓ hℓ3 hℓf))
    · have h2 : 2 ∣ q - 1 := by
        have : Odd q := hodd.pow
        obtain ⟨k, hk⟩ := this
        omega
      exact Nat.le_of_dvd hm0 (dvd_mL_of_prime Nat.prime_two (by norm_num) h2)
  refine ⟨hm2, fun j hj0 hjf hj2 => ?_⟩
  by_cases h2j : 2 * j = f
  ·
    left
    set s := p ^ j with hs
    have hs1 : 1 ≤ s := Nat.one_le_pow _ _ hp.pos
    have hs2 : 2 ≤ s := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have hqs : q = s * s := by rw [hq, hs, ← h2j, two_mul, pow_add]
    have hs3 : 3 ≤ s := by
      by_contra hlt
      have h : s = 2 := by omega
      rw [hqs, h] at h9
      norm_num at h9
    have hP := ordProj_three_le hs1
    rw [← hqs] at hP
    have hle : (s + 1) * (s - 1) ≤ (s + 1) * m := by
      calc (s + 1) * (s - 1) = q - 1 := by
            rw [hqs]
            zify [hs1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega) :
              s * s ≠ 0)]
            ring
        _ = 3 ^ (q - 1).factorization 3 * m := hqm.symm
        _ ≤ (s + 1) * m := Nat.mul_le_mul_right m hP
    have hm' : s - 1 ≤ m := Nat.le_of_mul_le_mul_left hle (by omega)
    omega
  · right
    intro hdvd
    by_cases h64 : q = 64
    · have hp2 : p = 2 := by
        have h2 : p ∣ 2 ^ 6 := by
          rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← h64, hq]
          exact dvd_pow_self p hf0
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      subst hp2
      have hf6 : f = 6 := Nat.pow_right_injective le_rfl (h64.trans (by norm_num))
      subst hf6
      have h7' : 7 ∣ 2 ^ j * (2 ^ (2 * j) - 1) :=
        (dvd_mul_of_dvd_right (h7 h64) 3).trans hdvd
      interval_cases j <;> revert h7' h2j hj2 <;> norm_num
    · have hf3 : 3 ≤ f := by
        by_contra hlt
        omega
      obtain ⟨ℓ, hℓ, hℓf, hℓk⟩ := hprim hf3 h64
      have hℓn : ℓ ∣ 3 * m := by
        by_cases hℓ3 : ℓ = 3
        · rw [hℓ3]
          exact dvd_mul_right 3 m
        · exact dvd_mul_of_dvd_right (dvd_mL_of_prime hℓ hℓ3 hℓf) 3
      have hℓp : ¬ ℓ ∣ p ^ j := by
        intro h
        have he := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow h)
        subst he
        have h1 : ℓ ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub (dvd_pow_self ℓ hf0) hℓf
        rw [Nat.sub_sub_self hq1] at h1
        exact hℓ.one_lt.ne' (Nat.dvd_one.1 h1)
      have h1 : ℓ ∣ p ^ (2 * j) - 1 :=
        ((Nat.Prime.dvd_mul hℓ).1 (hℓn.trans hdvd)).resolve_left hℓp
      have h2 := hord ℓ hℓ hℓf hℓk (2 * j) h1
      obtain ⟨t, ht⟩ := h2
      rcases t with _ | _ | t
      · omega
      · omega
      · nlinarith

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
