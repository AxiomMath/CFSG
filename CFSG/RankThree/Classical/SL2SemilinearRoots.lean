module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.RankThree.Classical

open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K : Type*} [Field K]

@[expose] def conjSL (M : GL (Fin 2) K) : SL(2, K) →* SL(2, K) where
  toFun A := ⟨(M : Matrix (Fin 2) (Fin 2) K) * A * (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, M.mul_inv, Matrix.det_one]⟩
  map_one' := Subtype.ext <| by
    change (M : Matrix (Fin 2) (Fin 2) K) * 1 * (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Matrix.mul_one]
    exact M.mul_inv
  map_mul' A B := Subtype.ext <| by
    change (M : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K) * B) *
        (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K) =
      (M : Matrix (Fin 2) (Fin 2) K) * A * (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K) *
        ((M : Matrix (Fin 2) (Fin 2) K) * B * (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K))
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K),
      M.inv_mul, Matrix.one_mul]

theorem coe_conjSL (M : GL (Fin 2) K) (A : SL(2, K)) :
    ((conjSL M A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (M : Matrix (Fin 2) (Fin 2) K) * A * (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem conjSL_mul (M N : GL (Fin 2) K) (A : SL(2, K)) :
    conjSL (M * N) A = conjSL M (conjSL N A) := by
  apply Subtype.ext
  change ((M * N : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
      (↑(M * N)⁻¹ : Matrix (Fin 2) (Fin 2) K) =
    (M : Matrix (Fin 2) (Fin 2) K) * ((N : Matrix (Fin 2) (Fin 2) K) * A *
      (↑N⁻¹ : Matrix (Fin 2) (Fin 2) K)) * (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K)
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem conjSL_one (A : SL(2, K)) : conjSL 1 A = A := by
  apply Subtype.ext
  change ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
      (↑(1 : GL (Fin 2) K)⁻¹ : Matrix (Fin 2) (Fin 2) K) = A
  rw [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def diagUnitOne (a : Kˣ) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : K), 0; 0, 1] (by simp [Matrix.det_fin_two])

theorem coe_diagUnitOne (a : Kˣ) :
    (diagUnitOne a : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, 1] :=
  rfl

theorem coe_diagUnitOne_inv (a : Kˣ) :
    (↑(diagUnitOne a)⁻¹ : Matrix (Fin 2) (Fin 2) K) = !![((a⁻¹ : Kˣ) : K), 0; 0, 1] := by
  rw [Matrix.coe_units_inv, coe_diagUnitOne]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] noncomputable def swapGL : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

theorem coe_swapGL : ((swapGL : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

theorem swapGL_mul_swapGL : (swapGL * swapGL : GL (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapGL_inv : (swapGL⁻¹ : GL (Fin 2) K) = swapGL :=
  inv_eq_of_mul_eq_one_left swapGL_mul_swapGL

theorem conjSL_sl2Upper (a : Kˣ) (c : K) :
    conjSL (diagUnitOne a) (sl2Upper K c) = sl2Upper K (a * c) := by
  ext i j
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv]
  fin_cases i <;> fin_cases j <;> simp

theorem conjSL_sl2Lower (a : Kˣ) (c : K) :
    conjSL (diagUnitOne a) (sl2Lower K c) = sl2Lower K (((a⁻¹ : Kˣ) : K) * c) := by
  ext i j
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem conjSL_swap_sl2Upper (c : K) : conjSL swapGL (sl2Upper K c) = sl2Lower K c := by
  ext i j
  rw [coe_conjSL, swapGL_inv, coe_swapGL]
  fin_cases i <;> fin_cases j <;> simp

theorem conjSL_swap_sl2Lower (c : K) : conjSL swapGL (sl2Lower K c) = sl2Upper K c := by
  ext i j
  rw [coe_conjSL, swapGL_inv, coe_swapGL]
  fin_cases i <;> fin_cases j <;> simp

theorem map_sl2Upper (σ : K ≃+* K) (c : K) :
    Matrix.SpecialLinearGroup.map (σ : K →+* K) (sl2Upper K c) = sl2Upper K (σ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_sl2Lower (σ : K ≃+* K) (c : K) :
    Matrix.SpecialLinearGroup.map (σ : K →+* K) (sl2Lower K c) = sl2Lower K (σ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem coe_zero_zero_eq_zero_of_mul_upper (X : SL(2, K)) {a : K} (ha : a ≠ 0) (b : K)
    (h : X * sl2Upper K a = sl2Lower K (-b) * X) : (X : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by
  have h01 := congrArg (fun Y : SL(2, K) => (Y : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower] at h01
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact h01.resolve_right ha

theorem sl2_semilinear_root_compatibility (σ : K ≃+* K) (a b : Kˣ) (T : SL(2, K) →* SL(2, K))
    (hu : ∀ c, T (sl2Upper K c) = sl2Upper K (a * σ c))
    (hl : ∀ c, T (sl2Lower K c) = sl2Lower K (b * σ c)) :
    a * b = 1 ∧ ∃ M : GL (Fin 2) K, (M : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, 1] ∧
      ∀ A : SL(2, K), ((T A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (M : Matrix (Fin 2) (Fin 2) K) *
          (Matrix.SpecialLinearGroup.map (σ : K →+* K) A : Matrix (Fin 2) (Fin 2) K) *
            (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K) := by
  have hab : a * b = 1 := by
    have hX : T (sl2Weyl K 1) = sl2Upper K a * sl2Lower K (-b) * sl2Upper K a := by
      rw [sl2Weyl_eq, map_mul, map_mul, hu, hl]
      simp
    have hrel : T (sl2Weyl K 1) * sl2Upper K a = sl2Lower K (-b) * T (sl2Weyl K 1) := by
      have h := congrArg T (sl2Weyl_mul_upper (1 : Kˣ) (1 : K))
      rw [map_mul, map_mul, hu, hl] at h
      simpa using h
    have h0 := coe_zero_zero_eq_zero_of_mul_upper _ a.ne_zero b hrel
    rw [hX, coe_upper_lower_upper_zero_zero] at h0
    exact Units.ext (by rw [Units.val_mul, Units.val_one]; linear_combination -h0)
  have hb : ((b : Kˣ) : K) = ((a⁻¹ : Kˣ) : K) := by
    rw [eq_inv_of_mul_eq_one_right hab]
  have hT : T = (conjSL (diagUnitOne a)).comp (Matrix.SpecialLinearGroup.map (σ : K →+* K)) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · rw [MonoidHom.comp_apply, map_sl2Upper, conjSL_sl2Upper, hu]
      · rw [MonoidHom.comp_apply, map_sl2Lower, conjSL_sl2Lower, hl, hb]
  refine ⟨hab, diagUnitOne a, coe_diagUnitOne a, fun A => ?_⟩
  rw [hT]
  rfl

theorem coe_swapGL_mul_diagUnitOne (a : Kˣ) :
    ((swapGL * diagUnitOne a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; (a : K), 0] := by
  rw [Units.val_mul, coe_swapGL, coe_diagUnitOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_semilinear_exchanged_root_compatibility (σ : K ≃+* K) (a b : Kˣ)
    (T : SL(2, K) →* SL(2, K)) (hu : ∀ c, T (sl2Upper K c) = sl2Lower K (a * σ c))
    (hl : ∀ c, T (sl2Lower K c) = sl2Upper K (b * σ c)) :
    a * b = 1 ∧ ∃ M : GL (Fin 2) K, (M : Matrix (Fin 2) (Fin 2) K) = !![0, 1; (a : K), 0] ∧
      ∀ A : SL(2, K), ((T A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (M : Matrix (Fin 2) (Fin 2) K) *
          (Matrix.SpecialLinearGroup.map (σ : K →+* K) A : Matrix (Fin 2) (Fin 2) K) *
            (↑M⁻¹ : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨hab, D, hD, hT⟩ := sl2_semilinear_root_compatibility σ a b ((conjSL swapGL).comp T)
    (fun c => by rw [MonoidHom.comp_apply, hu, conjSL_swap_sl2Lower])
    (fun c => by rw [MonoidHom.comp_apply, hl, conjSL_swap_sl2Upper])
  have hDa : D = diagUnitOne a := Units.ext (by rw [hD, coe_diagUnitOne])
  subst hDa
  refine ⟨hab, swapGL * diagUnitOne a, coe_swapGL_mul_diagUnitOne a, fun A => ?_⟩
  have hA : T A = conjSL swapGL (conjSL swapGL (T A)) := by
    rw [← conjSL_mul, swapGL_mul_swapGL, conjSL_one]
  have h2 := hT A
  rw [MonoidHom.comp_apply] at h2
  rw [hA, coe_conjSL, h2, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

end CFSG.RankThree.Classical
