module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.Open.StatedCenterThree

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace Item1117Res3Proof

open Matrix

variable {K : Type*} [Field K]

section Roots

variable {e : K} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
include he3 he1

theorem ne_zero_of_cube : e ≠ 0 := by
  rintro rfl
  simp at he3

theorem one_add_add_sq_eq_zero : 1 + e + e ^ 2 = 0 := by
  have h : (e - 1) * (1 + e + e ^ 2) = 0 := by linear_combination he3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) he1
  · exact h

theorem sq_ne_one_of_cube : e ^ 2 ≠ 1 := by
  intro h
  apply he1
  calc e = e * e ^ 2 := by rw [h, mul_one]
    _ = e ^ 3 := by ring
    _ = 1 := he3

theorem ne_sq_of_cube : e ≠ e ^ 2 := by
  intro h
  apply he1
  calc e = e ^ 2 := h
    _ = e * e := by ring
    _ = e ^ 2 * e := by rw [← h]
    _ = e ^ 3 := by ring
    _ = 1 := he3

theorem eq_one_or_of_cube {ζ : K} (hζ : ζ ^ 3 = 1) : ζ = 1 ∨ ζ = e ∨ ζ = e ^ 2 := by
  have h0 := one_add_add_sq_eq_zero he3 he1
  have h : (ζ - 1) * (ζ - e) * (ζ - e ^ 2) = 0 := by
    linear_combination hζ - he3 + (-ζ ^ 2 + e * ζ) * h0
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem injective_cycleTau : Function.Injective ![e, e ^ 2, (1 : K)] := by
  have h2 := sq_ne_one_of_cube he3 he1
  have h3 := ne_sq_of_cube he3 he1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons] at hij ⊢
  all_goals first
    | rfl
    | exact absurd hij h3
    | exact absurd hij he1
    | exact absurd hij.symm h3
    | exact absurd hij h2
    | exact absurd hij.symm he1
    | exact absurd hij.symm h2

end Roots

theorem eq_diagonal_of_commute {d : Fin 3 → K} (hd : Function.Injective d)
    {M : Matrix (Fin 3) (Fin 3) K} (hM : M * diagonal d = diagonal d * M) :
    M = diagonal fun i => M i i :=
  CFSG.Open.StatedCenterThree.eq_diagonal_of_commute hd hM

theorem entry_eq_zero_of_mul_eq {d : Fin 3 → K} {ζ : K} {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M * diagonal d = ζ • (diagonal d * M)) {i j : Fin 3} (hij : d j ≠ ζ * d i) :
    M i j = 0 := by
  have h := congrFun (congrFun hM i) j
  simp only [mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at h
  have h' : M i j * (d j - ζ * d i) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h' | h'
  · exact h'
  · exact absurd (sub_eq_zero.mp h') hij

section Patterns

variable {e : K} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
include he3 he1

theorem eq_cycE_of_mul_eq {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M * diagonal ![e, e ^ 2, 1] = e • (diagonal ![e, e ^ 2, 1] * M)) :
    M = !![0, M 0 1, 0; 0, 0, M 1 2; M 2 0, 0, 0] := by
  have h2 := sq_ne_one_of_cube he3 he1
  have h3 := ne_sq_of_cube he3 he1
  have z : ∀ i j : Fin 3, ![e, e ^ 2, (1 : K)] j ≠ e * ![e, e ^ 2, (1 : K)] i → M i j = 0 :=
    fun i j hij => entry_eq_zero_of_mul_eq hM hij
  ext i j
  fin_cases i <;> fin_cases j
  · exact z 0 0 (show e ≠ e * e from fun h => h3 (by linear_combination h))
  · rfl
  · exact z 0 2 (show (1 : K) ≠ e * e from fun h => h2 (by linear_combination -h))
  · exact z 1 0 (show e ≠ e * e ^ 2 from fun h => he1 (by linear_combination h + he3))
  · exact z 1 1 (show e ^ 2 ≠ e * e ^ 2 from fun h => h2 (by linear_combination h + he3))
  · rfl
  · rfl
  · exact z 2 1 (show e ^ 2 ≠ e * 1 from fun h => h3 (by linear_combination -h))
  · exact z 2 2 (show (1 : K) ≠ e * 1 from fun h => he1 (by linear_combination -h))

theorem eq_cycE2_of_mul_eq {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M * diagonal ![e, e ^ 2, 1] = e ^ 2 • (diagonal ![e, e ^ 2, 1] * M)) :
    M = !![0, 0, M 0 2; M 1 0, 0, 0; 0, M 2 1, 0] := by
  have h2 := sq_ne_one_of_cube he3 he1
  have h3 := ne_sq_of_cube he3 he1
  have z : ∀ i j : Fin 3, ![e, e ^ 2, (1 : K)] j ≠ e ^ 2 * ![e, e ^ 2, (1 : K)] i →
      M i j = 0 := fun i j hij => entry_eq_zero_of_mul_eq hM hij
  ext i j
  fin_cases i <;> fin_cases j
  · exact z 0 0 (show e ≠ e ^ 2 * e from fun h => he1 (by linear_combination h + he3))
  · exact z 0 1 (show e ^ 2 ≠ e ^ 2 * e from fun h => h2 (by linear_combination h + he3))
  · rfl
  · rfl
  · exact z 1 1 (show e ^ 2 ≠ e ^ 2 * e ^ 2 from fun h =>
      h3 (by linear_combination -h - e * he3))
  · exact z 1 2 (show (1 : K) ≠ e ^ 2 * e ^ 2 from fun h =>
      he1 (by linear_combination -h - e * he3))
  · exact z 2 0 (show e ≠ e ^ 2 * 1 from fun h => h3 (by linear_combination h))
  · rfl
  · exact z 2 2 (show (1 : K) ≠ e ^ 2 * 1 from fun h => h2 (by linear_combination -h))

end Patterns

theorem diagonal_mul_cycE (a b c m₀ m₁ m₂ : K) :
    diagonal ![a, b, c] * !![0, m₀, 0; 0, 0, m₁; m₂, 0, 0] =
      !![0, m₀, 0; 0, 0, m₁; m₂, 0, 0] * diagonal ![c, a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem diagonal_mul_cycE2 (a b c m₀ m₁ m₂ : K) :
    diagonal ![a, b, c] * !![0, 0, m₀; m₁, 0, 0; 0, m₂, 0] =
      !![0, 0, m₀; m₁, 0, 0; 0, m₂, 0] * diagonal ![b, c, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem eq_of_cycE_mul_diagonal {m₀ m₁ m₂ w₀ w₁ w₂ μ : K} (h₀ : m₀ ≠ 0) (h₁ : m₁ ≠ 0)
    (h₂ : m₂ ≠ 0)
    (h : !![0, m₀, 0; 0, 0, m₁; m₂, 0, 0] * diagonal ![w₀, w₁, w₂] =
      μ • (diagonal ![w₀, w₁, w₂] * !![0, m₀, 0; 0, 0, m₁; m₂, 0, 0])) :
    w₁ = μ * w₀ ∧ w₂ = μ * w₁ ∧ w₀ = μ * w₂ := by
  have e01 := congrFun (congrFun h 0) 1
  have e12 := congrFun (congrFun h 1) 2
  have e20 := congrFun (congrFun h 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e01 e12 e20
  refine ⟨?_, ?_, ?_⟩
  · have : m₀ * (w₁ - μ * w₀) = 0 := by linear_combination e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h₀)
  · have : m₁ * (w₂ - μ * w₁) = 0 := by linear_combination e12
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h₁)
  · have : m₂ * (w₀ - μ * w₂) = 0 := by linear_combination e20
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h₂)

theorem eq_of_cycE2_mul_diagonal {m₀ m₁ m₂ w₀ w₁ w₂ μ : K} (h₀ : m₀ ≠ 0) (h₁ : m₁ ≠ 0)
    (h₂ : m₂ ≠ 0)
    (h : !![0, 0, m₀; m₁, 0, 0; 0, m₂, 0] * diagonal ![w₀, w₁, w₂] =
      μ • (diagonal ![w₀, w₁, w₂] * !![0, 0, m₀; m₁, 0, 0; 0, m₂, 0])) :
    w₂ = μ * w₀ ∧ w₀ = μ * w₁ ∧ w₁ = μ * w₂ := by
  have e02 := congrFun (congrFun h 0) 2
  have e10 := congrFun (congrFun h 1) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e02 e10 e21
  refine ⟨?_, ?_, ?_⟩
  · have : m₀ * (w₂ - μ * w₀) = 0 := by linear_combination e02
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h₀)
  · have : m₁ * (w₀ - μ * w₁) = 0 := by linear_combination e10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h₁)
  · have : m₂ * (w₁ - μ * w₂) = 0 := by linear_combination e21
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h₂)

theorem det_cycE (m₀ m₁ m₂ : K) :
    (!![0, m₀, 0; 0, 0, m₁; m₂, 0, 0] : Matrix (Fin 3) (Fin 3) K).det = m₀ * m₁ * m₂ := by
  simp [Matrix.det_fin_three]

theorem det_cycE2 (m₀ m₁ m₂ : K) :
    (!![0, 0, m₀; m₁, 0, 0; 0, m₂, 0] : Matrix (Fin 3) (Fin 3) K).det = m₀ * m₁ * m₂ := by
  simp [Matrix.det_fin_three]

theorem trace_inv_mul_mul (Q : GL (Fin 3) K) (A : Matrix (Fin 3) (Fin 3) K) :
    (((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (Q : Matrix (Fin 3) (Fin 3) K)).trace =
      A.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem mul_scalar_eq_smul (M : Matrix (Fin 3) (Fin 3) K) (a : K) :
    M * Matrix.scalar (Fin 3) a = a • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]

theorem scalar_mul_eq_smul (M : Matrix (Fin 3) (Fin 3) K) (a : K) :
    Matrix.scalar (Fin 3) a * M = a • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem commute_of_commute_smul {A D : Matrix (Fin 3) (Fin 3) K} {c : K} (hc : c ≠ 0)
    (h : A * (c • D) = (c • D) * A) : A * D = D * A := by
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  calc A * D = c⁻¹ • (c • (A * D)) := (inv_smul_smul₀ hc _).symm
    _ = D * A := by rw [h, inv_smul_smul₀ hc]

theorem mul_eq_smul_of_smul {A D : Matrix (Fin 3) (Fin 3) K} {c ζ : K} (hc : c ≠ 0)
    (h : A * (c • D) = ζ • ((c • D) * A)) : A * D = ζ • (D * A) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm] at h
  calc A * D = c⁻¹ • (c • (A * D)) := (inv_smul_smul₀ hc _).symm
    _ = ζ • (D * A) := by rw [h, inv_smul_smul₀ hc]

theorem eq_vec_three {α : Type*} (v : Fin 3 → α) : v = ![v 0, v 1, v 2] := by
  funext i
  fin_cases i <;> rfl

theorem cycE_conj_diagonal {S S' : Matrix (Fin 3) (Fin 3) K} (hS : S' * S = 1)
    (hpat : S = !![0, S 0 1, 0; 0, 0, S 1 2; S 2 0, 0, 0]) (v : Fin 3 → K) :
    S' * diagonal v * S = diagonal ![v 2, v 0, v 1] := by
  have h1 : diagonal v * S = S * diagonal ![v 2, v 0, v 1] := by
    rw [eq_vec_three v, hpat, diagonal_mul_cycE]
    simp
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hS, Matrix.one_mul]

theorem cycE2_conj_diagonal {S S' : Matrix (Fin 3) (Fin 3) K} (hS : S' * S = 1)
    (hpat : S = !![0, 0, S 0 2; S 1 0, 0, 0; 0, S 2 1, 0]) (v : Fin 3 → K) :
    S' * diagonal v * S = diagonal ![v 1, v 2, v 0] := by
  have h1 : diagonal v * S = S * diagonal ![v 1, v 2, v 0] := by
    rw [eq_vec_three v, hpat, diagonal_mul_cycE2]
    simp
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hS, Matrix.one_mul]

theorem diagonal_mul_cyc_mul_cyc (v : Fin 3 → K) :
    diagonal v * diagonal ![v 2, v 0, v 1] * diagonal ![v 1, v 2, v 0] =
      (v 0 * v 1 * v 2) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one, ← diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, Pi.smul_apply, smul_eq_mul, mul_one] <;> ring

theorem diagonal_mul_cyc2_mul_cyc2 (v : Fin 3 → K) :
    diagonal v * diagonal ![v 1, v 2, v 0] * diagonal ![v 2, v 0, v 1] =
      (v 0 * v 1 * v 2) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one, ← diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, Pi.smul_apply, smul_eq_mul, mul_one] <;> ring

section Geometric

variable {e : K} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
include he3 he1

theorem exists_diagonal_geom_eq {ν : K} (hν : ν ^ 3 = 1) :
    ∃ (c : K) (k : ℕ), c ≠ 0 ∧ diagonal ![1, ν, ν ^ 2] = c • (diagonal ![e, e ^ 2, 1]) ^ k := by
  have he0 := ne_zero_of_cube he3 he1
  rcases eq_one_or_of_cube he3 he1 hν with h1 | h1 | h1 <;> subst ν
  · refine ⟨1, 0, one_ne_zero, ?_⟩
    rw [pow_zero, one_smul, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  · refine ⟨e ^ 2, 1, pow_ne_zero 2 he0, ?_⟩
    rw [pow_one, ← diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero,
      cons_val_one, cons_val_two, head_cons, tail_cons, Pi.smul_apply, smul_eq_mul, mul_one]
    · linear_combination -he3
    · linear_combination (-e) * he3
  · refine ⟨e, 2, he0, ?_⟩
    rw [diagonal_pow, ← diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero,
      cons_val_one, cons_val_two, head_cons, tail_cons, Pi.smul_apply, smul_eq_mul, Pi.pow_apply]
    · linear_combination -he3
    · linear_combination (-e ^ 2) * he3
    · linear_combination e * he3

end Geometric

end Item1117Res3Proof

end CFSG.RankThree.PartTwo.Sec11
