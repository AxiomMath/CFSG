module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

abbrev s16c11_case5_sigma : MulAut (VM K) := trM

theorem s16c11_case5_sigma_ofAdd (X : Matrix (Fin 2) (Fin 2) K) :
    s16c11_case5_sigma (Multiplicative.ofAdd X) = Multiplicative.ofAdd Xᵀ := by
  apply Multiplicative.toAdd.injective
  rw [s16c11_case5_sigma, toAdd_trM]
  rfl

theorem s16c11_case5_sigma_mul_self :
    (s16c11_case5_sigma (K := K)) * s16c11_case5_sigma = 1 :=
  trM_mul_self (K := K)

@[expose] noncomputable def s16c11_case5_sa (a : K) : MulAut (VM K) :=
  s16c11_case5_rhoU a a * s16c11_case5_sigma

theorem s16c11_case5_sa_toAdd (a : K) (X : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.toAdd (s16c11_case5_sa a (Multiplicative.ofAdd X)) =
      (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [s16c11_case5_sa, MulAut.mul_apply, s16c11_case5_sigma_ofAdd,
    s16c11_case5_rhoU_toAdd]

theorem s16c11_case5_actT_entry_00 (a : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 =
      X 0 0 + a * X 0 1 + a * X 1 0 + a * a * X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]
  ring

theorem s16c11_case5_actT_entry_01 (a : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1 =
      X 1 0 + a * X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]

theorem s16c11_case5_actT_entry_10 (a : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 0 =
      X 0 1 + a * X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]

theorem s16c11_case5_actT_entry_11 (a : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 1 =
      X 1 1 := by
  simp [s16c11_case5_u, tv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, mul_comm]

theorem s16c11_case5_sa_conds (a : K) (X : Matrix (Fin 2) (Fin 2) K) :
    (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ = X ↔
      a * (X 0 1 + X 1 0) + a * a * X 1 1 = 0 ∧ X 0 1 + X 1 0 + a * X 1 1 = 0 := by
  constructor
  · intro h
    have h00 : ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 = X 0 0 := by rw [h]
    have h01 : ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1 = X 0 1 := by rw [h]
    rw [s16c11_case5_actT_entry_00] at h00
    rw [s16c11_case5_actT_entry_01] at h01
    refine ⟨?_, ?_⟩
    · linear_combination h00
    · have hh : X 0 1 + X 1 0 + a * X 1 1 = 0 := by
        rw [← h01]; ring_nf; simp [CharTwo.two_eq_zero]
      exact hh
  · rintro ⟨h1, h2⟩
    ext i j
    fin_cases i <;> fin_cases j
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 0 = X 0 0
      rw [s16c11_case5_actT_entry_00]
      linear_combination h1
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1 = X 0 1
      rw [s16c11_case5_actT_entry_01]
      have hh : (X 1 0 + a * X 1 1) + X 0 1 = 0 := by
        rw [← h2]; ring
      rw [eq_neg_of_add_eq_zero_left hh, CharTwo.neg_eq]
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 0 = X 1 0
      rw [s16c11_case5_actT_entry_10]
      have hh : (X 0 1 + a * X 1 1) + X 1 0 = 0 := by
        rw [← h2]; ring
      rw [eq_neg_of_add_eq_zero_left hh, CharTwo.neg_eq]
    · change ((s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ) 1 1 = X 1 1
      rw [s16c11_case5_actT_entry_11]

theorem s16c11_case5_mem_fixV_sa_iff (a : K) (X : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.ofAdd X ∈ fixV (Subgroup.zpowers (s16c11_case5_sa a)) ↔
      (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K) * Xᵀ *
        (s16c11_case5_u a : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
  rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
  constructor
  · intro h
    have h2 := congrArg Multiplicative.toAdd h
    rwa [s16c11_case5_sa_toAdd] at h2
  · intro h
    apply Multiplicative.toAdd.injective
    rw [s16c11_case5_sa_toAdd, h]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
