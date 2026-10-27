module

public import CFSG.ClassicalInvolution.Phan.PhanS8Q3Ternary
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Tactic.LinearCombination
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenBlk

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.ClassicalInvolution.PhanB3.S.Std.Q

variable {K : Type} [Field K]

theorem exists_gram_normal_form [Finite K] (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 3) (Fin 3) K)
    (hs : Aᵀ = A) (hN : A.det ≠ 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) K, B.det ≠ 0 ∧ B * A * Bᵀ = (-A.det) • symGram K := by
  classical
  obtain ⟨a, ha0, haa⟩ := exists_isotropic A
  have hNa : A.mulVec a ≠ 0 := fun h => ha0 (Matrix.eq_zero_of_mulVec_eq_zero hN h)
  obtain ⟨i, hi⟩ : ∃ i, A.mulVec a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hNa (funext hcon)
  set m := A.mulVec a i with hm
  let y₀ : Fin 3 → K := Pi.single i 1
  have hy0a : Bf A y₀ a = m := by
    simp [Bf, y₀, hm]
  set B₀ := Bf A y₀ y₀ with hB₀
  set t := B₀ / (2 * m ^ 2) with ht
  set y : Fin 3 → K := m⁻¹ • y₀ + (-t) • a with hy
  have hay : Bf A y a = 1 := by
    rw [hy, Bf_add_left, Bf_smul_left, Bf_smul_left, hy0a, haa]
    field_simp
    ring
  have hya' : Bf A a y = 1 := by rw [Bf_comm' A hs]; exact hay
  have hyy : Bf A y y = 0 := by
    have hc := Bf_comm' A hs y₀ a
    rw [hy, Bf_add_left, Bf_add_right, Bf_add_right, Bf_smul_left, Bf_smul_left, Bf_smul_left,
      Bf_smul_left, Bf_smul_right, Bf_smul_right, Bf_smul_right, Bf_smul_right, ← hB₀,
      hy0a, ← hc, hy0a, haa, ht]
    field_simp
    ring
  set v : Fin 3 → K := A.adjugate *ᵥ cr a y with hv
  have hva : Bf A v a = 0 := Bf_adj_cr_left A hs a y
  have hvy : Bf A v y = 0 := Bf_adj_cr_right A hs a y
  have hvv : Bf A v v = -A.det := by
    have := Bf_adj_cr_self A hs a y
    rw [haa, hyy, hya'] at this
    rw [hv, this]
    ring
  have hav : Bf A a v = 0 := by rw [Bf_comm' A hs]; exact hva
  have hyv : Bf A y v = 0 := by rw [Bf_comm' A hs]; exact hvy
  let Mx : Matrix (Fin 3) (Fin 3) K := Matrix.of ![a, v, (2 * A.det) • y]
  have hG : Mx * A * Mxᵀ = (-A.det) • symGram K := by
    ext r c
    have e : (Mx * A * Mxᵀ) r c =
        Bf A (![a, v, (2 * A.det) • y] r) (![a, v, (2 * A.det) • y] c) := by
      rw [Bf_def]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
      fin_cases r <;> fin_cases c <;>
        simp only [Mx, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue,
          Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring
    rw [e]
    fin_cases r <;> fin_cases c <;>
      simp [symGram, Bf_smul_left, Bf_smul_right, haa, hya', hay, hav, hva, hyy, hvy, hyv, hvv] <;>
      ring
  refine ⟨Mx, ?_, hG⟩
  intro h0
  have hdsg : (symGram K).det = -4 := by
    simp [symGram, det_fin_three]
    ring
  have hdet := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_smul, hdsg] at hdet
  simp only [Fintype.card_fin] at hdet
  have h4 : A.det ^ 3 * 4 = 0 := by linear_combination (-1 : K) * hdet
  rcases mul_eq_zero.mp h4 with h | h
  · exact hN (pow_eq_zero_iff (by norm_num) |>.mp h)
  · exact h2 (by
      have : (2 : K) * 2 = 0 := by linear_combination h
      exact (mul_self_eq_zero.mp this))

end CFSG.Quasithin.SBd19F
