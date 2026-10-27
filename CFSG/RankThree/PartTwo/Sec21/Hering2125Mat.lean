module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open Matrix

variable {K : Type} [Field K]

@[expose] def uniM (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, a; b, 1, c; 0, 0, 1]

theorem uniM_mul (a b c a' b' c' : K) :
    uniM a b c * uniM a' b' c' = uniM (a + a') (b + b') (c + c' + b * a') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uniM_zero : uniM (0 : K) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniM]

theorem det_uniM (a b c : K) : (uniM a b c).det = 1 := by
  simp [uniM, Matrix.det_fin_three]

@[expose] def uniGL (a b c : K) : GL (Fin 3) K :=
  ⟨uniM a b c, uniM (-a) (-b) (a * b - c), by
    rw [uniM_mul]; convert uniM_zero using 2 <;> ring, by
    rw [uniM_mul]; convert uniM_zero using 2 <;> ring⟩

theorem uniGL_mul (a b c a' b' c' : K) :
    uniGL a b c * uniGL a' b' c' = uniGL (a + a') (b + b') (c + c' + b * a') := by
  ext1
  exact uniM_mul a b c a' b' c'

theorem uniGL_zero : uniGL (0 : K) 0 0 = 1 := by
  apply Units.ext
  exact uniM_zero

theorem uniGL_inv (a b c : K) : (uniGL a b c)⁻¹ = uniGL (-a) (-b) (a * b - c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [uniGL_mul, ← uniGL_zero]
  congr 1 <;> ring

theorem eq_one_of_mul_self [CharP K 2] {ν : K} (h : ν * ν = 1) : ν = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : (ν - 1) ^ 2 = 0 := by linear_combination h + (1 - ν) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)

theorem scalar_mem_center (ν : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) ν ∈ Subgroup.center (GL (Fin 3) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨ν, rfl⟩

theorem scalar_comm (ν : Kˣ) (g : GL (Fin 3) K) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 3) ν =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ν * g :=
  Subgroup.mem_center_iff.mp (scalar_mem_center ν) g

theorem scalar_eq_one {ν : Kˣ} (h : Matrix.GeneralLinearGroup.scalar (Fin 3) ν = 1) : ν = 1 := by
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp at this
  exact this

theorem eq_one_of_conj_sq [CharP K 2] {a b : GL (Fin 3) K} (ha : a * a = 1) {ν : Kˣ}
    (h : b * a * b⁻¹ = a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) : ν = 1 := by
  have h1 : (b * a * b⁻¹) * (b * a * b⁻¹) = 1 := by
    calc (b * a * b⁻¹) * (b * a * b⁻¹) = b * (a * a) * b⁻¹ := by group
      _ = 1 := by rw [ha]; group
  rw [h] at h1
  have h2 : a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν *
      (a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (ν * ν) := by
    calc a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν *
        (a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν)
        = a * (Matrix.GeneralLinearGroup.scalar (Fin 3) ν * a) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by group
      _ = a * (a * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by rw [← scalar_comm ν a]
      _ = (a * a) * (Matrix.GeneralLinearGroup.scalar (Fin 3) ν *
            Matrix.GeneralLinearGroup.scalar (Fin 3) ν) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (ν * ν) := by rw [ha, one_mul, map_mul]
  rw [h2] at h1
  have h3 := scalar_eq_one h1
  exact Units.ext (eq_one_of_mul_self (congrArg Units.val h3))

theorem exists_sq_eq [Finite K] [CharP K 2] (κ : Kˣ) : ∃ ρ : Kˣ, ρ * ρ = κ := by
  have hK : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hK (κ : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact κ.ne_zero (by simpa using hr)
  exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr.symm)⟩

theorem exists_sq_one_lift [Finite K] [CharP K 2] {b : GL (Fin 3) K}
    (h : Matrix.ProjGenLinGroup.mk b * Matrix.ProjGenLinGroup.mk b = 1) :
    ∃ b' : GL (Fin 3) K, Matrix.ProjGenLinGroup.mk b' = Matrix.ProjGenLinGroup.mk b ∧
      b' * b' = 1 := by
  have h1 : Matrix.ProjGenLinGroup.mk (b * b) = 1 := by rwa [map_mul]
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨μ, hμ⟩ := h1
  obtain ⟨ρ, hρ⟩ := exists_sq_eq μ
  refine ⟨b * Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹, ?_, ?_⟩
  · rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
  · have hs : ∀ g : GL (Fin 3) K,
        g * Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹ * g := fun g => scalar_comm _ g
    calc b * Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹ *
          (b * Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹)
        = b * (Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹ * b) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹ := by group
      _ = b * (b * Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹ := by rw [← hs b]
      _ = (b * b) * (Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹ *
            Matrix.GeneralLinearGroup.scalar (Fin 3) ρ⁻¹) := by group
      _ = 1 := by
        rw [← hμ, ← map_mul, ← map_mul, ← hρ, show ρ * ρ * (ρ⁻¹ * ρ⁻¹) = 1 by group, map_one]

theorem shape_of_comm_uni {g : GL (Fin 3) K}
    (h : g * uniGL 0 0 1 = uniGL 0 0 1 * g) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 1 1 = (g : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  have h' : (g : Matrix (Fin 3) (Fin 3) K) * uniM 0 0 1 =
      uniM 0 0 1 * (g : Matrix (Fin 3) (Fin 3) K) := congrArg Units.val h
  have e01 := congrFun (congrFun h' 0) 2
  have e20 := congrFun (congrFun h' 1) 0
  have e21 := congrFun (congrFun h' 1) 1
  have e11 := congrFun (congrFun h' 1) 2
  simp [uniM, Matrix.mul_apply, Fin.sum_univ_three] at e01 e20 e21 e11
  exact ⟨e01, e20, e21, by linear_combination e11⟩

theorem entries_of_comm_diag {D b : GL (Fin 3) K} {e₀ : K} (he₀ : e₀ ≠ 1)
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![e₀, 1, 1])
    (h : b * D = D * b) :
    (b : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (b : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (b : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (b : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  have h' : (b : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ![e₀, 1, 1] =
      Matrix.diagonal ![e₀, 1, 1] * (b : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hD]; exact congrArg Units.val h
  have e01 := congrFun (congrFun h' 0) 1
  have e02 := congrFun (congrFun h' 0) 2
  have e10 := congrFun (congrFun h' 1) 0
  have e20 := congrFun (congrFun h' 2) 0
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at e01 e02 e10 e20
  have hne : e₀ - 1 ≠ 0 := sub_ne_zero.mpr he₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (e₀ - 1) * (b : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left hne
  · have : (e₀ - 1) * (b : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by linear_combination -e02
    exact (mul_eq_zero.mp this).resolve_left hne
  · have : (e₀ - 1) * (b : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_left hne
  · have : (e₀ - 1) * (b : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by linear_combination e20
    exact (mul_eq_zero.mp this).resolve_left hne

theorem eq_uniGL_of_comm [CharP K 2] {D b : GL (Fin 3) K} {e₀ : K} (he₀ : e₀ ≠ 1)
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![e₀, 1, 1])
    (hb : b * b = 1) (hbD : b * D = D * b) (hbu : b * uniGL 0 0 1 = uniGL 0 0 1 * b) :
    ∃ q : K, b = uniGL 0 0 q := by
  obtain ⟨h01, h02, h10, h20⟩ := entries_of_comm_diag he₀ hD hbD
  obtain ⟨-, -, h21, h1122⟩ := shape_of_comm_uni hbu
  have hb' : (b : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, hb]; rfl
  have e00 := congrFun (congrFun hb' 0) 0
  have e11 := congrFun (congrFun hb' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e11
  have h00 : (b : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    apply eq_one_of_mul_self
    rw [h01, h02, h10, h20] at e00
    linear_combination e00
  have h11 : (b : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    apply eq_one_of_mul_self
    rw [h10, h21] at e11
    linear_combination e11
  refine ⟨(b : Matrix (Fin 3) (Fin 3) K) 1 2, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniGL, uniM, h00, h01, h02, h10, h20, h21, h11, h1122]
  · rw [← h1122, h11]

theorem conj_uniGL {g : GL (Fin 3) K}
    (h01 : (g : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h1122 : (g : Matrix (Fin 3) (Fin 3) K) 1 1 = (g : Matrix (Fin 3) (Fin 3) K) 2 2)
    (a b c : K) : ∃ a' b' c' : K, g * uniGL a b c * g⁻¹ = uniGL a' b' c' := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    simpa using this
  rw [Matrix.det_fin_three, h01, h20, h21, h1122] at hdet
  have h00 : (g : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h; apply hdet; rw [h]; ring
  have h22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h; apply hdet; rw [h]; ring
  set g00 := (g : Matrix (Fin 3) (Fin 3) K) 0 0
  set g02 := (g : Matrix (Fin 3) (Fin 3) K) 0 2
  set g10 := (g : Matrix (Fin 3) (Fin 3) K) 1 0
  set g12 := (g : Matrix (Fin 3) (Fin 3) K) 1 2
  set l := (g : Matrix (Fin 3) (Fin 3) K) 2 2
  refine ⟨a * g00 / l, b * l / g00, (a * g10 + c * l - g02 * (b * l / g00)) / l, ?_⟩
  have key : g * uniGL a b c = uniGL (a * g00 / l) (b * l / g00)
      ((a * g10 + c * l - g02 * (b * l / g00)) / l) * g := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uniGL, uniM, Matrix.mul_apply, Fin.sum_univ_three, h01, h20, h21, h1122] <;>
      field_simp <;> ring
  rw [mul_inv_eq_iff_eq_mul]
  exact key

theorem comm_diag_of_block {P : GL (Fin 3) K} {D : GL (Fin 3) K} {e₀ : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![e₀, 1, 1])
    (h01 : (P : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) (h02 : (P : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (h10 : (P : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (h20 : (P : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) :
    D * P = P * D := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, h01, h02, h10, h20] <;> ring

theorem exists_basis_change [CharP K 2] {D a : GL (Fin 3) K} {e₀ : K} (he₀ : e₀ ≠ 1)
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![e₀, 1, 1])
    (ha : a * a = 1) (haD : a * D = D * a) (hne : a ≠ 1) :
    ∃ P : GL (Fin 3) K, a * P = P * uniGL 0 0 1 ∧ D * P = P * D := by
  obtain ⟨h01, h02, h10, h20⟩ := entries_of_comm_diag he₀ hD haD
  have ha' : (a : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, ha]; rfl
  have e00 := congrFun (congrFun ha' 0) 0
  have e11 := congrFun (congrFun ha' 1) 1
  have e12 := congrFun (congrFun ha' 1) 2
  have e21 := congrFun (congrFun ha' 2) 1
  have e22 := congrFun (congrFun ha' 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e11 e12 e21 e22
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h00 : (a : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    apply eq_one_of_mul_self
    rw [h01, h02, h10, h20] at e00
    linear_combination e00
  rw [h10] at e11 e12
  rw [h20] at e21 e22
  by_cases hr : (a : Matrix (Fin 3) (Fin 3) K) 2 1 = 0
  ·
    have ha11 : (a : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
      apply eq_one_of_mul_self
      rw [hr] at e11
      linear_combination e11
    have ha22 : (a : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      apply eq_one_of_mul_self
      rw [hr] at e22
      linear_combination e22
    have hq : (a : Matrix (Fin 3) (Fin 3) K) 1 2 ≠ 0 := by
      intro hq
      apply hne
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h20, ha11, ha22, hr, hq]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![1, 0, 0; 0, (a : Matrix (Fin 3) (Fin 3) K) 1 2, 0; 0, 0, 1] ?_, ?_, ?_⟩
    · simp [Matrix.det_fin_three, hq]
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, uniGL, uniM, h00, h01, h02, h10, h20, ha11,
          ha22, hr]
    · exact comm_diag_of_block hD (by simp) (by simp) (by simp) (by simp)
  ·
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![1, 0, 0; 0, (a : Matrix (Fin 3) (Fin 3) K) 1 1 + 1, 1;
        0, (a : Matrix (Fin 3) (Fin 3) K) 2 1, 0] ?_, ?_, ?_⟩
    · simp [Matrix.det_fin_three, hr]
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, uniGL, uniM, h00, h01, h02, h10, h20]
      all_goals
        first
        | linear_combination e11
        | linear_combination (-1 : K) * h2
        | linear_combination e21
    · exact comm_diag_of_block hD (by simp) (by simp) (by simp) (by simp)

theorem diag_conj_uni {D : GL (Fin 3) K} {e₀ : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![e₀, 1, 1]) (a : K) :
    D * uniGL a 0 0 = uniGL (e₀ * a) 0 0 * D := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniGL, uniM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem det_conj_uniGL (P : GL (Fin 3) K) (a b c : K) :
    ((P * uniGL a b c * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h := Matrix.GeneralLinearGroup.val_det_apply (P * uniGL a b c * P⁻¹)
  rw [← h, map_mul, map_mul, map_inv]
  have : ((Matrix.GeneralLinearGroup.det (uniGL a b c) : Kˣ) : K) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_uniM a b c
  have h2 : Matrix.GeneralLinearGroup.det (uniGL a b c) = 1 := Units.ext this
  rw [h2]
  simp

end CFSG.RankThree.PartTwo.Sec21.Hering2125
