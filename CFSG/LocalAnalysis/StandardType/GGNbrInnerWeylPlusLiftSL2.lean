module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib

public section

namespace CFSG.StandardType.GGPlusLiftSL2

open CFSG.LieType.Chevalley Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_orderOf_eq_prime_sl2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : ∃ s : SL2 K, orderOf s = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine exists_prime_orderOf_dvd_card' p ?_
  have hdvd : p ∣ Nat.card K ^ 2 - 1 :=
    dvd_trans hpq ⟨Nat.card K - 1, by simpa using Nat.pow_two_sub_pow_two (Nat.card K) 1⟩
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, mul_comm]
  exact dvd_mul_of_dvd_left hdvd (Nat.card K)

theorem exists_order_p_inverting_sl2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) :
    ∃ s n : SL2 K, orderOf s = p ∧ n * s * n⁻¹ = s⁻¹ := by
  classical
  obtain ⟨s, hsorder⟩ := exists_orderOf_eq_prime_sl2 (K := K) hp hp2 hpq
  have hs_pow : s ^ p = 1 := by rw [← hsorder]; exact pow_orderOf_eq_one s
  set a : K := (s : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b : K := (s : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c : K := (s : Matrix (Fin 2) (Fin 2) K) 1 0 with hcdef
  set d : K := (s : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h := s.2
    rw [Matrix.det_fin_two] at h
    rwa [← ha, ← hb, ← hcdef, ← hd] at h
  have hdet' : a * d + b * c = 1 := by
    rw [← CharTwo.sub_eq_add]
    exact hdet
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hpow00 : ∀ k : ℕ, ((s : Matrix (Fin 2) (Fin 2) K) ^ k) 0 0 = a ^ k := by
      intro k
      induction k with
      | zero => simp [ha]
      | succ k ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, ih, ← ha, ← hcdef, hc0, mul_zero,
          add_zero, pow_succ]
    have hap : a ^ p = 1 := by
      have h1 : ((s : Matrix (Fin 2) (Fin 2) K) ^ p) 0 0 = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_pow, hs_pow, Matrix.SpecialLinearGroup.coe_one]
        simp
      rwa [hpow00 p] at h1
    have ha_ne : a ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hap
      exact zero_ne_one hap
    let u : Kˣ := Units.mk0 a ha_ne
    have hu_pow : u ^ p = 1 := by
      apply Units.ext
      simpa [u] using hap
    have hord1 : orderOf u = 1 := by
      rcases hp.eq_one_or_self_of_dvd (orderOf u) (orderOf_dvd_of_pow_eq_one hu_pow) with h1 | hp'
      · exact h1
      · exfalso
        have hp_dvd : p ∣ Nat.card K - 1 := by
          rw [← Nat.card_units (α := K), ← hp']
          exact orderOf_dvd_natCard u
        have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
          have h1 : p ≤ Nat.card K + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
          have h2 : 2 ≤ p := hp.two_le
          omega
        have h2d : p ∣ 2 := by
          rw [← hsub]
          exact Nat.dvd_sub hpq hp_dvd
        exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2d) hp.two_le)
    have ha1 : a = 1 := by
      have hu1 : u = 1 := by rw [← orderOf_eq_one_iff]; exact hord1
      simpa [u] using congrArg Units.val hu1
    have hd1 : d = 1 := by
      have h := hdet
      rw [ha1, hc0, one_mul, mul_zero, sub_zero] at h
      exact h
    have hs_eq : (s : Matrix (Fin 2) (Fin 2) K) = !![1, b; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [← ha, ← hb, ← hcdef, ← hd, ha1, hc0, hd1]
    have hs2 : s ^ 2 = 1 := by
      apply Subtype.ext
      rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, hs_eq, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CharTwo.add_self_eq_zero]
    have hp_dvd2 : p ∣ 2 := by
      have h : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one hs2
      rwa [hsorder] at h
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hp_dvd2) hp.two_le)
  have hdet_n : a * a - (a ^ 2 + 1) = 1 := by
    rw [CharTwo.sub_eq_add, ← pow_two, ← add_assoc, ← two_mul, CharTwo.two_eq_zero, zero_mul,
      zero_add]
  have hcy : c * ((a ^ 2 + 1) * c⁻¹) = a ^ 2 + 1 := by
    rw [← mul_assoc, mul_comm c (a ^ 2 + 1), mul_assoc, mul_inv_cancel₀ hc_ne, mul_one]
  have hyc : ((a ^ 2 + 1) * c⁻¹) * c = a ^ 2 + 1 := by
    rw [mul_comm ((a ^ 2 + 1) * c⁻¹) c, hcy]
  have hlhs00 : a * a + (a ^ 2 + 1) = 1 := by
    rw [← pow_two, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hrhs00 : d * a + b * c = 1 := by
    rw [mul_comm d a]
    exact hdet'
  have hlhs11 : c * b + a * d = 1 := by
    rw [mul_comm c b, add_comm]
    exact hdet'
  have hrhs11 : (a ^ 2 + 1) + a * a = 1 := by
    rw [← pow_two, add_comm (a ^ 2 + 1) (a ^ 2), ← add_assoc, CharTwo.add_self_eq_zero,
      zero_add]
  have hs_eq : (s : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [← ha, ← hb, ← hcdef, ← hd]
  have hsInv : ((s⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![d, b; c, a] := by
    change adjugate (s : Matrix (Fin 2) (Fin 2) K) = !![d, b; c, a]
    rw [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [← ha, ← hb, ← hcdef, ← hd, CharTwo.neg_eq]
  let nMat : Matrix (Fin 2) (Fin 2) K := !![a, (a ^ 2 + 1) * c⁻¹; c, a]
  have hnDet : nMat.det = 1 := by
    change (!![a, (a ^ 2 + 1) * c⁻¹; c, a] : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [Matrix.det_fin_two]
    show a * a - ((a ^ 2 + 1) * c⁻¹) * c = 1
    rw [hyc]
    exact hdet_n
  let n : SL2 K := ⟨nMat, hnDet⟩
  refine ⟨s, n, hsorder, ?_⟩
  have hns : n * s = s⁻¹ * n := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hsInv]
    change nMat * (s : Matrix (Fin 2) (Fin 2) K) = !![d, b; c, a] * nMat
    show !![a, (a ^ 2 + 1) * c⁻¹; c, a] * (s : Matrix (Fin 2) (Fin 2) K) =
      !![d, b; c, a] * !![a, (a ^ 2 + 1) * c⁻¹; c, a]
    rw [hs_eq, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp <;>
      first
        | rw [hyc, hlhs00, hrhs00]
        | rw [hcy, hlhs11, hrhs11]
        | ring
  rw [hns, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.StandardType.GGPlusLiftSL2

end
