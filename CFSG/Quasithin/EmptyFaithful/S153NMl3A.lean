module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.S153N

open CFSG.Assembly.LowTwoRank Matrix

namespace Ml3

variable {K : Type} [Field K]

theorem exists_matrix_order_three (i : Fin 3) :
    ∃ B : Matrix (Fin 3) (Fin 3) K, B ^ 3 = 1 ∧ B ≠ 1 ∧ B.det = 1 ∧
      B.mulVec (Pi.single i 1) = Pi.single i 1 := by
  fin_cases i
  · refine ⟨!![1, 0, 0; 0, 0, -1; 0, 1, -1], ?_, ?_, ?_, ?_⟩
    · rw [pow_succ, pow_two]
      simp only [Matrix.mul_fin_three]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro h
      have := congrFun (congrFun h 1) 1
      simp at this
    · simp [Matrix.det_fin_three]
    · ext j
      fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine ⟨!![0, 0, -1; 0, 1, 0; 1, 0, -1], ?_, ?_, ?_, ?_⟩
    · rw [pow_succ, pow_two]
      simp only [Matrix.mul_fin_three]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro h
      have := congrFun (congrFun h 0) 0
      simp at this
    · simp [Matrix.det_fin_three]
    · ext j
      fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ?_, ?_, ?_, ?_⟩
    · rw [pow_succ, pow_two]
      simp only [Matrix.mul_fin_three]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro h
      have := congrFun (congrFun h 0) 0
      simp at this
    · simp [Matrix.det_fin_three]
    · ext j
      fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_conj_order_three (G : GL (Fin 3) K) (i : Fin 3) :
    ∃ ρ : ↥(StatedSL 3 K), ρ ≠ 1 ∧ ρ ^ 3 = 1 ∧
      ((ρ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
        ((G : Matrix (Fin 3) (Fin 3) K).mulVec (Pi.single i 1)) =
      (G : Matrix (Fin 3) (Fin 3) K).mulVec (Pi.single i 1) := by
  obtain ⟨B, hB3, hB1, hBdet, hBfix⟩ := exists_matrix_order_three (K := K) i
  have hBdet' : B.det ≠ 0 := by rw [hBdet]; exact one_ne_zero
  set Bg : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet' with hBg
  have hBgv : (Bg : Matrix (Fin 3) (Fin 3) K) = B := rfl
  have hBg1 : Bg ≠ 1 := fun h => hB1 (by rw [← hBgv, h]; rfl)
  have hBg3 : Bg ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hBgv, hB3]
    rfl
  have hGinv : ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (G : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : ((G * Bg * G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det *
        (G : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.det_mul, hGinv, Matrix.det_one]
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hBgv, hBdet]
    calc (G : Matrix (Fin 3) (Fin 3) K).det * 1 *
          ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det
        = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det *
          (G : Matrix (Fin 3) (Fin 3) K).det := by ring
      _ = 1 := h1
  have hmem : (G * Bg * G⁻¹ : GL (Fin 3) K) ∈ StatedSL 3 K := Subgroup.subset_closure hdet
  refine ⟨⟨G * Bg * G⁻¹, hmem⟩, ?_, ?_, ?_⟩
  · intro h
    have h' : G * Bg * G⁻¹ = 1 := congrArg Subtype.val h
    apply hBg1
    have : Bg = G⁻¹ * (G * Bg * G⁻¹) * G := by group
    rw [this, h']
    group
  · apply Subtype.ext
    show (G * Bg * G⁻¹) ^ 3 = 1
    rw [conj_pow, hBg3, mul_one, mul_inv_cancel]
  · show ((G * Bg * G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec _ = _
    have e : (G : Matrix (Fin 3) (Fin 3) K) * B *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K) =
        (G : Matrix (Fin 3) (Fin 3) K) * B := by
      rw [Matrix.mul_assoc ((G : Matrix (Fin 3) (Fin 3) K) * B), hGinv, Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, hBgv, Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hBfix]

theorem exists_statedSL_order_three (x : Fin 3 → K) :
    ∃ ρ : ↥(StatedSL 3 K), ρ ≠ 1 ∧ ρ ^ 3 = 1 ∧
      ((ρ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x = x := by
  by_cases hx : x = 0
  · obtain ⟨ρ, h1, h3, -⟩ := exists_conj_order_three (1 : GL (Fin 3) K) 0
    exact ⟨ρ, h1, h3, by rw [hx, Matrix.mulVec_zero]⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hdet : (Matrix.updateCol (1 : Matrix (Fin 3) (Fin 3) K) i x).det = x i := by
      rw [← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    set G : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.updateCol (1 : Matrix (Fin 3) (Fin 3) K) i x) (by rw [hdet]; exact hi) with hG
    obtain ⟨ρ, h1, h3, hfix⟩ := exists_conj_order_three G i
    refine ⟨ρ, h1, h3, ?_⟩
    have hGe : (G : Matrix (Fin 3) (Fin 3) K).mulVec (Pi.single i 1) = x := by
      rw [Matrix.mulVec_single_one]
      funext j
      exact Matrix.updateCol_self
    rwa [hGe] at hfix

end Ml3

end CFSG.Quasithin.S153N
