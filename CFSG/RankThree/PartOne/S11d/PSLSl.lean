module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.RankThree.PartOne

open Matrix

variable {m : ℕ} {K : Type} [Field K]

@[expose] def tvSL (i j : Fin m) (hij : i ≠ j) (c : K) : SpecialLinearGroup (Fin m) K :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem coe_tvSL (i j : Fin m) (hij : i ≠ j) (c : K) :
    ((tvSL i j hij c : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      transvection i j c := rfl

theorem tvSL_mul_same (i j : Fin m) (hij : i ≠ j) (c d : K) :
    tvSL i j hij c * tvSL i j hij d = tvSL i j hij (c + d) :=
  Subtype.ext (transvection_mul_transvection_same i j hij c d)

theorem tvSL_sq [CharP K 2] (i j : Fin m) (hij : i ≠ j) :
    tvSL i j hij (1 : K) * tvSL i j hij 1 = 1 := by
  rw [tvSL_mul_same, show (1 : K) + 1 = 0 from by
    rw [← two_mul, show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_mul]]
  exact Subtype.ext (transvection_zero i j)

theorem map_tvSL (σ : K ≃+* K) (i j : Fin m) (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.map σ.toRingHom (tvSL i j hij c) = tvSL i j hij (σ c) := by
  apply Subtype.ext
  ext a b
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [coe_tvSL, transvection, Matrix.single_apply_same, hij]
  · simp [coe_tvSL, transvection, Matrix.one_apply, h]

theorem coe_tvSL_apply_self (i j : Fin m) (hij : i ≠ j) (c : K) :
    ((tvSL i j hij c : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) i j = c := by
  simp [coe_tvSL, transvection, Matrix.single_apply_same, hij]


theorem transvection_mul_apply_self (i j : Fin m) (hij : i ≠ j) :
    ((transvection i j (1 : K) * transvection j i 1 : Matrix (Fin m) (Fin m) K) i i = 1 + 1) ∧
      ((transvection j i (1 : K) * transvection i j 1 : Matrix (Fin m) (Fin m) K) i i = 1) := by
  constructor
  · simp [transvection, add_mul, mul_add, Matrix.single_mul_single_same, hij.symm]
  · simp [transvection, add_mul, mul_add, Matrix.single_mul_single_same, hij.symm]

theorem tvSL_comm_ne [CharP K 2] (i j : Fin m) (hij : i ≠ j) {z : K}
    (h : ((tvSL i j hij (1 : K) * tvSL j i hij.symm 1 : SpecialLinearGroup (Fin m) K) :
        Matrix (Fin m) (Fin m) K) =
      z • ((tvSL j i hij.symm (1 : K) * tvSL i j hij 1 : SpecialLinearGroup (Fin m) K) :
        Matrix (Fin m) (Fin m) K)) : z = 0 := by
  obtain ⟨h1, h2⟩ := transvection_mul_apply_self (K := K) i j hij
  have := congrFun (congrFun h i) i
  simp only [Matrix.smul_apply, smul_eq_mul, SpecialLinearGroup.coe_mul] at this
  change (transvection i j (1 : K) * transvection j i 1 : Matrix (Fin m) (Fin m) K) i i =
    z * (transvection j i (1 : K) * transvection i j 1 : Matrix (Fin m) (Fin m) K) i i at this
  rw [h1, h2, mul_one, show (1 : K) + 1 = 0 from by
    rw [← two_mul, show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_mul]] at this
  exact this.symm

theorem not_inner_map {σ : K ≃+* K} (hσ : σ ≠ 1) (i j : Fin m) (hij : i ≠ j)
    (N : SpecialLinearGroup (Fin m) K)
    (h : ∀ s : SpecialLinearGroup (Fin m) K, SpecialLinearGroup.map σ.toRingHom s = N * s * N⁻¹) :
    False := by
  have h1 := h (tvSL i j hij 1)
  rw [map_tvSL, map_one] at h1
  have hN : N * tvSL i j hij 1 = tvSL i j hij 1 * N := by
    calc N * tvSL i j hij 1 = N * tvSL i j hij 1 * N⁻¹ * N := (inv_mul_cancel_right _ _).symm
      _ = tvSL i j hij 1 * N := by rw [← h1]
  have hNE : (N : Matrix (Fin m) (Fin m) K) * Matrix.single i j 1 =
      Matrix.single i j 1 * (N : Matrix (Fin m) (Fin m) K) := by
    have := congrArg (fun g : SpecialLinearGroup (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) hN
    simp only [SpecialLinearGroup.coe_mul, coe_tvSL, transvection, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact add_left_cancel this
  apply hσ
  ext c
  have h2 := h (tvSL i j hij c)
  rw [map_tvSL] at h2
  have hNc : N * tvSL i j hij c = tvSL i j hij c * N := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
    simp only [coe_tvSL, transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul]
    have : (Matrix.single i j c : Matrix (Fin m) (Fin m) K) = c • Matrix.single i j 1 := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, hNE]
  have h3 : tvSL i j hij (σ c) = tvSL i j hij c := by
    rw [h2, hNc, mul_assoc, mul_inv_cancel, mul_one]
  have h4 := congrArg
    (fun g : SpecialLinearGroup (Fin m) K => (g : Matrix (Fin m) (Fin m) K) i j) h3
  simp only [coe_tvSL_apply_self] at h4
  exact h4

end CFSG.RankThree.PartOne
