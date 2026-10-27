module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3Core

public section

namespace CFSG.Quasithin.H13.L829NK.L3OutA

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
open CFSG.Quasithin.L3Aut CFSG.Quasithin.L3Aut.Core

variable {K : Type*} [Field K]

@[expose] def diagSL (a b : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹], by
    have ha : (a : K) ≠ 0 := a.ne_zero
    have hb : (b : K) ≠ 0 := b.ne_zero
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue]
    field_simp⟩

@[simp] theorem coe_diagSL (a b : Kˣ) :
    ((diagSL a b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹] := rfl

@[expose] def wMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

@[expose] def wSL : SpecialLinearGroup (Fin 3) K :=
  ⟨wMat, by simp [wMat, Matrix.det_fin_three]⟩

theorem cube_eq_one_of_rel {A D : Matrix (Fin 3) (Fin 3) K} {c : K} (hD : D.det = 1)
    (hA : A.det ≠ 0) (h : D * A = c • (A * D)) : c ^ 3 = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin, hD] at h1
  have : (c ^ 3 - 1) * A.det = 0 := by linear_combination -h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hA)

theorem entry_rel {A : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} {c : K}
    (h : diagonal d * A = c • (A * diagonal d)) (i j : Fin 3) :
    d i * A i j = c * (A i j * d j) := by
  have := congrFun (congrFun h i) j
  simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply] using this

theorem rel_of_proj_comm (g h : SpecialLinearGroup (Fin 3) K)
    (H : proj 3 K g * proj 3 K h = proj 3 K h * proj 3 K g) :
    ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) =
      c • ((h : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) := by
  rw [← map_mul, ← map_mul] at H
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp H)
  have key : ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((g * h)⁻¹ * (h * g) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((h * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul (g * h) ((g * h)⁻¹ * (h * g)), mul_inv_cancel_left]
  have hgh : ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) :=
    Matrix.SpecialLinearGroup.coe_mul g h
  have hhg : ((h * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (h : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) :=
    Matrix.SpecialLinearGroup.coe_mul h g
  rw [hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one,
    hgh, hhg] at key
  refine ⟨(c⁻¹ : Kˣ), ?_⟩
  rw [← key, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ c.ne_zero, one_smul]

theorem entry_rel_left {A : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} {c : K}
    (h : A * diagonal d = c • (diagonal d * A)) (i j : Fin 3) :
    A i j * d j = c * (d i * A i j) := by
  have := congrFun (congrFun h i) j
  simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply] using this

theorem key_matrix (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (h1 : ∃ c : K, M * diagonal ![1, -1, -1] = c • (diagonal ![1, -1, -1] * M))
    (hw : ∃ c : K, M * wMat = c • (wMat * M)) :
    ∃ a e : K, M = diagonal ![a, a, e] := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨c', hc'⟩ := hw
  have r00 : M 0 0 * 1 = c * (1 * M 0 0) := entry_rel_left hc 0 0
  have r01 : M 0 1 * (-1) = c * (1 * M 0 1) := entry_rel_left hc 0 1
  have r02 : M 0 2 * (-1) = c * (1 * M 0 2) := entry_rel_left hc 0 2
  have r10 : M 1 0 * 1 = c * (-1 * M 1 0) := entry_rel_left hc 1 0
  have r11 : M 1 1 * (-1) = c * (-1 * M 1 1) := entry_rel_left hc 1 1
  have r12 : M 1 2 * (-1) = c * (-1 * M 1 2) := entry_rel_left hc 1 2
  have r20 : M 2 0 * 1 = c * (-1 * M 2 0) := entry_rel_left hc 2 0
  have r21 : M 2 1 * (-1) = c * (-1 * M 2 1) := entry_rel_left hc 2 1
  have r22 : M 2 2 * (-1) = c * (-1 * M 2 2) := entry_rel_left hc 2 2
  have hc1 : c = 1 := by
    by_contra hne
    have hne' : c - 1 ≠ 0 := sub_ne_zero.mpr hne
    have m00 : M 0 0 = 0 := by
      have : (c - 1) * M 0 0 = 0 := by linear_combination -r00
      exact (mul_eq_zero.mp this).resolve_left hne'
    have m11 : M 1 1 = 0 := by
      have : (c - 1) * M 1 1 = 0 := by linear_combination r11
      exact (mul_eq_zero.mp this).resolve_left hne'
    have m22 : M 2 2 = 0 := by
      have : (c - 1) * M 2 2 = 0 := by linear_combination r22
      exact (mul_eq_zero.mp this).resolve_left hne'
    have m12 : M 1 2 = 0 := by
      have : (c - 1) * M 1 2 = 0 := by linear_combination r12
      exact (mul_eq_zero.mp this).resolve_left hne'
    have m21 : M 2 1 = 0 := by
      have : (c - 1) * M 2 1 = 0 := by linear_combination r21
      exact (mul_eq_zero.mp this).resolve_left hne'
    have hd0 : M.det = 0 := by
      rw [Matrix.det_fin_three]
      simp [m00, m11, m22, m12, m21]
    rw [hd0] at hdet
    exact zero_ne_one hdet
  subst hc1
  have m01 : M 0 1 = 0 := by
    have : (2 : K) * M 0 1 = 0 := by linear_combination -r01
    exact (mul_eq_zero.mp this).resolve_left h2
  have m02 : M 0 2 = 0 := by
    have : (2 : K) * M 0 2 = 0 := by linear_combination -r02
    exact (mul_eq_zero.mp this).resolve_left h2
  have m10 : M 1 0 = 0 := by
    have : (2 : K) * M 1 0 = 0 := by linear_combination r10
    exact (mul_eq_zero.mp this).resolve_left h2
  have m20 : M 2 0 = 0 := by
    have : (2 : K) * M 2 0 = 0 := by linear_combination r20
    exact (mul_eq_zero.mp this).resolve_left h2
  have s12 : M 1 0 * 0 + M 1 1 * 0 + M 1 2 * (-1) =
      c' * (1 * M 0 2 + 0 * M 1 2 + 0 * M 2 2) := by
    have := congrFun (congrFun hc' 1) 2
    simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three, wMat,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons] using this
  have s20 : M 2 0 * 0 + M 2 1 * 1 + M 2 2 * 0 = c' * (0 * M 0 0 + 0 * M 1 0 + (-1) * M 2 0) := by
    have := congrFun (congrFun hc' 2) 0
    simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three, wMat,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons] using this
  have s22 :
      M 2 0 * 0 + M 2 1 * 0 + M 2 2 * (-1) = c' * (0 * M 0 2 + 0 * M 1 2 + (-1) * M 2 2) := by
    have := congrFun (congrFun hc' 2) 2
    simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three, wMat,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons] using this
  have s01 : M 0 0 * 1 + M 0 1 * 0 + M 0 2 * 0 = c' * (0 * M 0 1 + 1 * M 1 1 + 0 * M 2 1) := by
    have := congrFun (congrFun hc' 0) 1
    simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three, wMat,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons] using this
  have m12 : M 1 2 = 0 := by linear_combination (-1 : K) * s12 + (-c') * m02
  have m21 : M 2 1 = 0 := by linear_combination s20 - c' * m20
  have hdet' : M 0 0 * M 1 1 * M 2 2 = 1 := by
    rw [Matrix.det_fin_three] at hdet
    simp only [m01, m02, m10, m20, m12, m21] at hdet
    linear_combination hdet
  have hε : M 2 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet'
    exact zero_ne_one hdet'
  have hc'1 : c' = 1 := by
    have : M 2 2 * (c' - 1) = 0 := by linear_combination s22
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hε)
  subst hc'1
  have hβ : M 1 1 = M 0 0 := by linear_combination -s01
  refine ⟨M 0 0, M 2 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m20, m12, m21, hβ]

theorem ne_neg_one_of_cube (h2 : (2 : K) ≠ 0) {c : K} (hc : c ^ 3 = 1) : c ≠ -1 := by
  rintro rfl
  apply h2
  linear_combination -hc

theorem det_diag_pm (x y z : K) (h : x * y * z = 1) : (diagonal ![x, y, z]).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simpa using h

theorem zero_of_neg_one (h2 : (2 : K) ≠ 0) {c x : K} (hc : c ^ 3 = 1)
    (hx : (-1 : K) * x = c * (x * 1)) : x = 0 := by
  have hne : 1 + c ≠ 0 := by
    intro hh
    apply ne_neg_one_of_cube h2 hc
    linear_combination hh
  have : (1 + c) * x = 0 := by linear_combination -hx
  exact (mul_eq_zero.mp this).resolve_left hne

theorem offdiag_zero (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 3) (Fin 3) K) (hA : A.det ≠ 0)
    (hD0 : ∃ c : K, diagonal ![1, -1, -1] * A = c • (A * diagonal ![1, -1, -1]))
    (hD1 : ∃ c : K, diagonal ![-1, 1, -1] * A = c • (A * diagonal ![-1, 1, -1]))
    (hD2 : ∃ c : K, diagonal ![-1, -1, 1] * A = c • (A * diagonal ![-1, -1, 1])) :
    A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 1 0 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 := by
  obtain ⟨c0, h0⟩ := hD0
  obtain ⟨c1, h1⟩ := hD1
  obtain ⟨c2, h2'⟩ := hD2
  have k0 := cube_eq_one_of_rel (det_diag_pm 1 (-1) (-1) (by ring)) hA h0
  have k1 := cube_eq_one_of_rel (det_diag_pm (-1) 1 (-1) (by ring)) hA h1
  have k2 := cube_eq_one_of_rel (det_diag_pm (-1) (-1) 1 (by ring)) hA h2'
  have e01 : (-1 : K) * A 0 1 = c1 * (A 0 1 * 1) := entry_rel h1 0 1
  have e02 : (-1 : K) * A 0 2 = c2 * (A 0 2 * 1) := entry_rel h2' 0 2
  have e10 : (-1 : K) * A 1 0 = c0 * (A 1 0 * 1) := entry_rel h0 1 0
  have e12 : (-1 : K) * A 1 2 = c2 * (A 1 2 * 1) := entry_rel h2' 1 2
  have e20 : (-1 : K) * A 2 0 = c0 * (A 2 0 * 1) := entry_rel h0 2 0
  have e21 : (-1 : K) * A 2 1 = c1 * (A 2 1 * 1) := entry_rel h1 2 1
  exact ⟨zero_of_neg_one h2 k1 e01, zero_of_neg_one h2 k2 e02, zero_of_neg_one h2 k0 e10,
    zero_of_neg_one h2 k2 e12, zero_of_neg_one h2 k0 e20, zero_of_neg_one h2 k1 e21⟩

theorem det_of_offdiag_zero (A : Matrix (Fin 3) (Fin 3) K) (h01 : A 0 1 = 0) (h02 : A 0 2 = 0)
    (h10 : A 1 0 = 0) (h12 : A 1 2 = 0) (h20 : A 2 0 = 0) (h21 : A 2 1 = 0) :
    A.det = A 0 0 * A 1 1 * A 2 2 := by
  rw [Matrix.det_fin_three, h01, h02, h10, h12, h20, h21]
  ring

theorem diag_eq_of_x12 (A : Matrix (Fin 3) (Fin 3) K) (hA : A.det ≠ 0)
    (h01 : A 0 1 = 0) (h02 : A 0 2 = 0) (h10 : A 1 0 = 0) (h12 : A 1 2 = 0) (h20 : A 2 0 = 0)
    (h21 : A 2 1 = 0) (c : K)
    (hx : (x12 (1 : K) : Matrix (Fin 3) (Fin 3) K) * A =
      c • (A * (x12 (1 : K) : Matrix (Fin 3) (Fin 3) K))) :
    c = 1 ∧ A 1 1 = A 0 0 := by
  have hd := det_of_offdiag_zero A h01 h02 h10 h12 h20 h21
  have hA00 : A 0 0 ≠ 0 := by
    intro h; apply hA; rw [hd, h]; ring
  have a00 := congrFun (congrFun hx 0) 0
  have a01 := congrFun (congrFun hx 0) 1
  simp only [coe_x12, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, h01, h02, h10, h12, h20, h21] at a00 a01
  have hc : c = 1 := by
    have : (c - 1) * A 0 0 = 0 := by linear_combination -a00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hA00)
  refine ⟨hc, ?_⟩
  rw [hc] at a01
  linear_combination a01

theorem coe_inv_transpose_diagSL (a b : Kˣ) :
    (((diagSL a b)⁻¹).transpose : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(a : K)⁻¹, (b : K)⁻¹, ((a : K)⁻¹ * (b : K)⁻¹)⁻¹] := by
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hb : (b : K) ≠ 0 := b.ne_zero
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv, coe_diagSL,
    Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.transpose_apply] <;>
    field_simp

theorem fix_diag0 (A : GeneralLinearGroup (Fin 3) K) (a b : Kˣ)
    (h : conjAut 3 K A (proj 3 K (diagSL a b)) = proj 3 K (diagSL a b)) :
    ∃ c : K, diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹] * (A : Matrix (Fin 3) (Fin 3) K) =
      c • ((A : Matrix (Fin 3) (Fin 3) K) * diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹]) := by
  rw [conjAut_proj] at h
  obtain ⟨c, hc⟩ := fix_matrix h
  exact ⟨c, hc⟩

theorem fix_diag1 (A : GeneralLinearGroup (Fin 3) K) (a b : Kˣ)
    (h : conjAut 3 K A (dualAut 3 K (proj 3 K (diagSL a b))) = proj 3 K (diagSL a b)) :
    ∃ c : K, diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹] * (A : Matrix (Fin 3) (Fin 3) K) =
      c • ((A : Matrix (Fin 3) (Fin 3) K) *
        (((diagSL a b)⁻¹).transpose : Matrix (Fin 3) (Fin 3) K)) := by
  rw [dualAut_proj, conjAut_proj] at h
  obtain ⟨c, hc⟩ := fix_matrix h
  exact ⟨c, hc⟩

@[expose] def x13 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem conjAut_toGL (d : SpecialLinearGroup (Fin 3) K) :
    conjAut 3 K (Matrix.SpecialLinearGroup.toGL d) = MulAut.conj (proj 3 K d) := by
  ext p
  obtain ⟨g, rfl⟩ := proj_surjective 3 K p
  have hc : CatalogueBHigherLinearAction.slConjugation 3 K (Matrix.SpecialLinearGroup.toGL d) g =
      d * g * d⁻¹ :=
    Matrix.SpecialLinearGroup.toGL_injective (by
      rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv])
  rw [conjAut_proj, hc, map_mul, map_mul, map_inv, MulAut.conj_apply]

theorem coe_x13 : ((x13 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![1, 0, 1; 0, 1, 0; 0, 0, 1] := rfl

theorem torus_inner (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) [Finite K]
    (hσ : ∀ σ : K ≃+* K, σ = 1) (ψ : MulAut (projectiveSL 3 K)) (hψ : ψ * ψ = 1)
    (ht : ∀ a b : Kˣ, ψ (proj 3 K (diagSL a b)) = proj 3 K (diagSL a b))
    (hx : ψ (proj 3 K (x12 (1 : K))) = proj 3 K (x12 (1 : K))) :
    ∃ x : projectiveSL 3 K, ψ = MulAut.conj x := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen ψ
  obtain rfl := hσ σ
  simp only [map_one, mul_one] at hψ ht hx ⊢
  have hA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := GeneralLinearGroup.det_ne_zero A
  interval_cases ε
  ·
    simp only [pow_zero, mul_one] at hψ ht hx ⊢
    have hD0 : ∃ c : K, diagonal ![1, -1, -1] * (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, -1, -1]) := by
      obtain ⟨c, hc⟩ := fix_diag0 A 1 (-1) (ht 1 (-1))
      exact ⟨c, by simpa using hc⟩
    have hD1 : ∃ c : K, diagonal ![-1, 1, -1] * (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, 1, -1]) := by
      obtain ⟨c, hc⟩ := fix_diag0 A (-1) 1 (ht (-1) 1)
      exact ⟨c, by simpa using hc⟩
    have hD2 : ∃ c : K, diagonal ![-1, -1, 1] * (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, -1, 1]) := by
      obtain ⟨c, hc⟩ := fix_diag0 A (-1) (-1) (ht (-1) (-1))
      exact ⟨c, by simpa using hc⟩
    obtain ⟨h01, h02, h10, h12, h20, h21⟩ := offdiag_zero h2 _ hA hD0 hD1 hD2
    obtain ⟨cx, hcx⟩ := fix_matrix (A := A) (g := x12 (1 : K)) (h := x12 (1 : K)) (by
      have := hx
      rw [conjAut_proj] at this
      exact this)
    obtain ⟨-, hA11⟩ := diag_eq_of_x12 (A : Matrix (Fin 3) (Fin 3) K) hA h01 h02 h10 h12 h20 h21
      cx hcx
    have hdet := det_of_offdiag_zero (A : Matrix (Fin 3) (Fin 3) K) h01 h02 h10 h12 h20 h21
    obtain ⟨a, e, hAd⟩ : ∃ a e : K, (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, e] := by
      refine ⟨(A : Matrix (Fin 3) (Fin 3) K) 0 0, (A : Matrix (Fin 3) (Fin 3) K) 2 2, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h01, h02, h10, h12, h20, h21, hA11, Matrix.diagonal]
    have hne : a * a * e ≠ 0 := by
      have : (A : Matrix (Fin 3) (Fin 3) K).det = a * a * e := by
        rw [hAd, Matrix.det_diagonal, Fin.prod_univ_three]
        simp
      rw [← this]
      exact hA
    have ha : a ≠ 0 := fun h => hne (by rw [h]; ring)
    have he : e ≠ 0 := fun h => hne (by rw [h]; ring)
    have hAA : conjAut 3 K (A * A) = 1 := by rw [map_mul]; exact hψ
    have hfix13 : proj 3 K (CatalogueBHigherLinearAction.slConjugation 3 K (A * A) (x13 (K := K))) =
        proj 3 K (x13 (K := K)) := by
      have := congrArg (fun f : MulAut (projectiveSL 3 K) => f (proj 3 K (x13 (K := K)))) hAA
      simpa [conjAut_proj] using this
    obtain ⟨c13, hc13⟩ := fix_matrix hfix13
    rw [Units.val_mul, hAd] at hc13
    have b00 := congrFun (congrFun hc13 0) 0
    have b02 := congrFun (congrFun hc13 0) 2
    simp [coe_x13, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] at b00 b02
    have hc13' : c13 = 1 := by
      have : (c13 - 1) * (a * a) = 0 := by linear_combination -b00
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero ha ha))
    have hee : e * e = a * a := by
      rw [hc13'] at b02
      linear_combination b02
    rcases mul_self_eq_mul_self_iff.mp hee with h | h
    ·
      refine ⟨1, ?_⟩
      have hAs : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha) := by
        apply Units.ext
        rw [hAd, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply, h]
        congr 1
        ext i
        fin_cases i <;> rfl
      rw [hAs, conjAut_scalar, map_one]
    ·
      refine ⟨proj 3 K (diagSL (K := K) (-1) (-1)), ?_⟩
      have hAs : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (-a) (neg_ne_zero.mpr ha)) *
          Matrix.SpecialLinearGroup.toGL (diagSL (K := K) (-1) (-1)) := by
        apply Units.ext
        rw [Units.val_mul, hAd, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
        show diagonal ![a, a, e] =
          diagonal (fun _ => -a) *
            ((diagSL (K := K) (-1) (-1) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        rw [coe_diagSL, Matrix.diagonal_mul_diagonal, h]
        congr 1
        ext i
        fin_cases i <;> simp
      rw [hAs, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  ·
    exfalso
    simp only [pow_one] at hψ ht hx
    have ht' : ∀ a b : Kˣ, conjAut 3 K A (dualAut 3 K (proj 3 K (diagSL a b))) =
        proj 3 K (diagSL a b) := fun a b => ht a b
    have hD0 : ∃ c : K, diagonal ![1, -1, -1] * (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, -1, -1]) := by
      obtain ⟨c, hc⟩ := fix_diag1 A 1 (-1) (ht' 1 (-1))
      rw [coe_inv_transpose_diagSL] at hc
      exact ⟨c, by simpa using hc⟩
    have hD1 : ∃ c : K, diagonal ![-1, 1, -1] * (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, 1, -1]) := by
      obtain ⟨c, hc⟩ := fix_diag1 A (-1) 1 (ht' (-1) 1)
      rw [coe_inv_transpose_diagSL] at hc
      exact ⟨c, by simpa using hc⟩
    have hD2 : ∃ c : K, diagonal ![-1, -1, 1] * (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, -1, 1]) := by
      obtain ⟨c, hc⟩ := fix_diag1 A (-1) (-1) (ht' (-1) (-1))
      rw [coe_inv_transpose_diagSL] at hc
      exact ⟨c, by simpa using hc⟩
    obtain ⟨h01, h02, h10, h12, h20, h21⟩ := offdiag_zero h2 _ hA hD0 hD1 hD2
    have hdet := det_of_offdiag_zero (A : Matrix (Fin 3) (Fin 3) K) h01 h02 h10 h12 h20 h21
    have hne : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
        (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
      rw [← hdet]
      exact hA
    have hA00 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h => hne (by rw [h]; ring)
    have hA11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := fun h => hne (by rw [h]; ring)
    obtain ⟨c, hc⟩ := fix_diag1 A (Units.mk0 2 h2) 1 (ht' (Units.mk0 2 h2) 1)
    rw [coe_inv_transpose_diagSL] at hc
    have e00 : (2 : K) * (A : Matrix (Fin 3) (Fin 3) K) 0 0 =
        c * ((A : Matrix (Fin 3) (Fin 3) K) 0 0 * 2⁻¹) := by
      have := congrFun (congrFun hc 0) 0
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
    have e11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 = c * (A : Matrix (Fin 3) (Fin 3) K) 1 1 := by
      have := congrFun (congrFun hc 1) 1
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
    have hc1 : c = 1 := by
      have : (c - 1) * (A : Matrix (Fin 3) (Fin 3) K) 1 1 = 0 := by linear_combination -e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hA11)
    have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    have h4 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (4 - c) = 0 := by
      linear_combination 2 * e00 + (c * (A : Matrix (Fin 3) (Fin 3) K) 0 0) * hinv
    have h4' : (4 : K) - c = 0 := (mul_eq_zero.mp h4).resolve_left hA00
    apply h3
    linear_combination h4' + hc1

@[expose] def d0SL : SpecialLinearGroup (Fin 3) K := diagSL (K := K) 1 (-1)

theorem coe_d0SL : ((d0SL : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    diagonal ![1, -1, -1] := by
  simp [d0SL, coe_diagSL]

@[expose] def Em0 : Matrix (Fin 3) (Fin 3) K := (1 : Matrix (Fin 3) (Fin 3) K)

@[expose] def Em1 : Matrix (Fin 3) (Fin 3) K := diagonal ![1, -1, -1]

@[expose] def Em2 : Matrix (Fin 3) (Fin 3) K := wMat

@[expose] def Em3 : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; -1, 0, 0; 0, 0, 1]

@[expose] def Em4 : Matrix (Fin 3) (Fin 3) K := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def Em5 : Matrix (Fin 3) (Fin 3) K := diagonal ![-1, -1, 1]

@[expose] def Em6 : Matrix (Fin 3) (Fin 3) K := diagonal ![-1, 1, -1]

@[expose] def Em7 : Matrix (Fin 3) (Fin 3) K := !![0, -1, 0; -1, 0, 0; 0, 0, -1]
@[expose] def EM : Set (Matrix (Fin 3) (Fin 3) K) :=
  {Em0, Em1, Em2, Em3, Em4, Em5, Em6, Em7}
theorem mem_EM0 : (Em0 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]
theorem mem_EM1 : (Em1 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]
theorem mem_EM2 : (Em2 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]
theorem mem_EM3 : (Em3 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]
theorem mem_EM4 : (Em4 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]
theorem mem_EM5 : (Em5 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]
theorem mem_EM6 : (Em6 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]
theorem mem_EM7 : (Em7 : Matrix (Fin 3) (Fin 3) K) ∈ EM := by
  simp [EM]

theorem Em0_mul_d0 : Em0 * diagonal ![(1 : K), -1, -1] = Em1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em0, Em1, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em0_mul_w : Em0 * (wMat (K := K)) = Em2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em0, Em2, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em1_mul_d0 : Em1 * diagonal ![(1 : K), -1, -1] = Em0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em1, Em0, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em1_mul_w : Em1 * (wMat (K := K)) = Em3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em1, Em3, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em2_mul_d0 : Em2 * diagonal ![(1 : K), -1, -1] = Em4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em2, Em4, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em2_mul_w : Em2 * (wMat (K := K)) = Em0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em2, Em0, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em3_mul_d0 : Em3 * diagonal ![(1 : K), -1, -1] = Em7 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em3, Em7, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em3_mul_w : Em3 * (wMat (K := K)) = Em1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em3, Em1, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em4_mul_d0 : Em4 * diagonal ![(1 : K), -1, -1] = Em2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em4, Em2, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em4_mul_w : Em4 * (wMat (K := K)) = Em6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em4, Em6, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em5_mul_d0 : Em5 * diagonal ![(1 : K), -1, -1] = Em6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em5, Em6, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em5_mul_w : Em5 * (wMat (K := K)) = Em7 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em5, Em7, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em6_mul_d0 : Em6 * diagonal ![(1 : K), -1, -1] = Em5 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em6, Em5, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em6_mul_w : Em6 * (wMat (K := K)) = Em4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em6, Em4, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em7_mul_d0 : Em7 * diagonal ![(1 : K), -1, -1] = Em3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em7, Em3, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em7_mul_w : Em7 * (wMat (K := K)) = Em5 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em7, Em5, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem EM_mul_gens {M : Matrix (Fin 3) (Fin 3) K} (hM : M ∈ EM (K := K)) :
    M * diagonal ![1, -1, -1] ∈ EM (K := K) ∧ M * wMat ∈ EM (K := K) := by
  simp only [EM, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Em0_mul_d0, Em0_mul_w]; exact ⟨mem_EM1, mem_EM2⟩
  · rw [Em1_mul_d0, Em1_mul_w]; exact ⟨mem_EM0, mem_EM3⟩
  · rw [Em2_mul_d0, Em2_mul_w]; exact ⟨mem_EM4, mem_EM0⟩
  · rw [Em3_mul_d0, Em3_mul_w]; exact ⟨mem_EM7, mem_EM1⟩
  · rw [Em4_mul_d0, Em4_mul_w]; exact ⟨mem_EM2, mem_EM6⟩
  · rw [Em5_mul_d0, Em5_mul_w]; exact ⟨mem_EM6, mem_EM7⟩
  · rw [Em6_mul_d0, Em6_mul_w]; exact ⟨mem_EM5, mem_EM4⟩
  · rw [Em7_mul_d0, Em7_mul_w]; exact ⟨mem_EM3, mem_EM5⟩

theorem EM_sq {M : Matrix (Fin 3) (Fin 3) K} (hM : M ∈ EM (K := K)) :
    M * M = 1 ∨ M * M = (Em5 : Matrix (Fin 3) (Fin 3) K) := by
  simp only [EM, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em0, Matrix.mul_apply, Fin.sum_univ_three, wMat]
  · left; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em1, Matrix.mul_apply, Fin.sum_univ_three, wMat]
  · left; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em2, Matrix.mul_apply, Fin.sum_univ_three, wMat]
  · right; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em3, Em5, Matrix.mul_apply, Fin.sum_univ_three]
  · right; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em4, Em5, Matrix.mul_apply, Fin.sum_univ_three]
  · left; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em5, Matrix.mul_apply, Fin.sum_univ_three, wMat]
  · left; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em6, Matrix.mul_apply, Fin.sum_univ_three, wMat]
  · left; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Em7, Matrix.mul_apply, Fin.sum_univ_three, wMat]

theorem Em5_mul_Em5 : (Em5 : Matrix (Fin 3) (Fin 3) K) * Em5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em5]

theorem EM_pow_four {M : Matrix (Fin 3) (Fin 3) K} (hM : M ∈ EM (K := K)) : M ^ 4 = 1 := by
  have h4 : M ^ 4 = (M * M) * (M * M) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4]
  rcases EM_sq hM with h | h <;> rw [h]
  · exact mul_one 1
  · exact Em5_mul_Em5

theorem d0SL_mul_self : d0SL (K := K) * d0SL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_d0SL, diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem wSL_mul_self : wSL (K := K) * wSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change wMat * wMat = (1 : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def HP : Subgroup (projectiveSL 3 K) :=
  Subgroup.closure {proj 3 K (d0SL (K := K)), proj 3 K (wSL (K := K))}

theorem closure_EM {g : projectiveSL 3 K} (hg : g ∈ HP (K := K)) :
    ∃ M ∈ EM (K := K), ∃ e : SpecialLinearGroup (Fin 3) K,
      (e : Matrix (Fin 3) (Fin 3) K) = M ∧ proj 3 K e = g := by
  have hi1 : (proj 3 K (d0SL (K := K)))⁻¹ = proj 3 K (d0SL (K := K)) := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right d0SL_mul_self]
  have hi2 : (proj 3 K (wSL (K := K)))⁻¹ = proj 3 K (wSL (K := K)) := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right wSL_mul_self]
  refine Subgroup.closure_induction_right
    (p := fun x _ => ∃ M ∈ EM (K := K), ∃ e : SpecialLinearGroup (Fin 3) K,
      (e : Matrix (Fin 3) (Fin 3) K) = M ∧ proj 3 K e = x) ?_ ?_ ?_ hg
  · exact ⟨Em0, mem_EM0, 1, by simp [Em0], map_one _⟩
  · intro x _ y hy ih
    obtain ⟨M, hM, e, he, rfl⟩ := ih
    rcases hy with rfl | rfl
    · refine ⟨M * diagonal ![1, -1, -1], (EM_mul_gens hM).1, e * d0SL, ?_, by rw [map_mul]⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, he, coe_d0SL]
    · refine ⟨M * wMat, (EM_mul_gens hM).2, e * wSL, ?_, by rw [map_mul]⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, he]
      rfl
  · intro x _ y hy ih
    obtain ⟨M, hM, e, he, rfl⟩ := ih
    rcases hy with rfl | rfl
    · rw [hi1]
      refine ⟨M * diagonal ![1, -1, -1], (EM_mul_gens hM).1, e * d0SL, ?_, by rw [map_mul]⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, he, coe_d0SL]
    · rw [hi2]
      refine ⟨M * wMat, (EM_mul_gens hM).2, e * wSL, ?_, by rw [map_mul]⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, he]
      rfl

theorem isPGroup_HP : IsPGroup 2 (HP (K := K)) := by
  intro g
  obtain ⟨M, hM, e, he, hpe⟩ := closure_EM g.2
  refine ⟨2, ?_⟩
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  apply Subtype.ext
  have he4 : e ^ 4 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, he, EM_pow_four hM]
    rfl
  rw [Subgroup.coe_pow, ← hpe, ← map_pow, he4, map_one]
  rfl

theorem centralizer_HP (h2 : (2 : K) ≠ 0) (m : projectiveSL 3 K)
    (hd : m * proj 3 K (d0SL (K := K)) = proj 3 K (d0SL (K := K)) * m)
    (hw : m * proj 3 K (wSL (K := K)) = proj 3 K (wSL (K := K)) * m) :
    ∃ g : SpecialLinearGroup (Fin 3) K, m = proj 3 K g ∧
      ∃ a e : K, (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, e] := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K m
  obtain ⟨c1, hc1⟩ := rel_of_proj_comm g (d0SL (K := K)) hd
  obtain ⟨c2, hc2⟩ := rel_of_proj_comm g (wSL (K := K)) hw
  rw [coe_d0SL] at hc1
  obtain ⟨a, e, hae⟩ := key_matrix h2 (g : Matrix (Fin 3) (Fin 3) K)
    (Matrix.SpecialLinearGroup.det_coe g) ⟨c1, hc1⟩ ⟨c2, hc2⟩
  exact ⟨g, rfl, a, e, hae⟩

theorem proj_comm_diagSL {g : SpecialLinearGroup (Fin 3) K} {a e : K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, e]) (a' b' : Kˣ) :
    proj 3 K g * proj 3 K (diagSL (K := K) a' b') =
      proj 3 K (diagSL (K := K) a' b') * proj 3 K g := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, coe_diagSL,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem proj_comm_x12 {g : SpecialLinearGroup (Fin 3) K} {a e : K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, e]) :
    proj 3 K g * proj 3 K (x12 (1 : K)) = proj 3 K (x12 (1 : K)) * proj 3 K g := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, coe_x12]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]

theorem commute_tests (h2 : (2 : K) ≠ 0) (m : projectiveSL 3 K)
    (hd : m * proj 3 K (d0SL (K := K)) = proj 3 K (d0SL (K := K)) * m)
    (hw : m * proj 3 K (wSL (K := K)) = proj 3 K (wSL (K := K)) * m) :
    (∀ a b : Kˣ, m * proj 3 K (diagSL (K := K) a b) = proj 3 K (diagSL (K := K) a b) * m) ∧
      m * proj 3 K (x12 (1 : K)) = proj 3 K (x12 (1 : K)) * m := by
  obtain ⟨g, rfl, a, e, hae⟩ := centralizer_HP h2 m hd hw
  exact ⟨fun a' b' => proj_comm_diagSL hae a' b', proj_comm_x12 hae⟩

end CFSG.Quasithin.H13.L829NK.L3OutA
