module

public import CFSG.Quasithin.Vol2.Ch11SecB414MI
public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open Matrix

variable {F : Type} [Field F]

abbrev dgv (c : F) : Fin 3 → F := ![c, 1, 1]

theorem dgv_mul_dgv (c d : F) (i : Fin 3) : dgv c i * dgv d i = dgv (c * d) i := by
  fin_cases i <;> simp

@[expose] noncomputable def dgHom : Fˣ →* GL (Fin 3) F where
  toFun c := ⟨diagonal (dgv (c : F)), diagonal (dgv ((c⁻¹ : Fˣ) : F)), by
      rw [diagonal_mul_diagonal]
      convert diagonal_one (n := Fin 3) (α := F) using 2
      ext i
      rw [dgv_mul_dgv, Units.mul_inv]
      fin_cases i <;> simp, by
      rw [diagonal_mul_diagonal]
      convert diagonal_one (n := Fin 3) (α := F) using 2
      ext i
      rw [dgv_mul_dgv, Units.inv_mul]
      fin_cases i <;> simp⟩
  map_one' := by
    apply Units.ext
    show diagonal (dgv ((1 : Fˣ) : F)) = 1
    rw [Units.val_one, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  map_mul' c d := by
    apply Units.ext
    show diagonal (dgv ((c * d : Fˣ) : F)) = diagonal (dgv (c : F)) * diagonal (dgv (d : F))
    rw [diagonal_mul_diagonal, Units.val_mul]
    congr 1
    ext i
    rw [dgv_mul_dgv]

theorem coe_dgHom (c : Fˣ) : ((dgHom c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    diagonal (dgv (c : F)) := rfl

theorem coe_dgHom_inv (c : Fˣ) : (((dgHom c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    diagonal (dgv ((c⁻¹ : Fˣ) : F)) := rfl

theorem twAdj_dg_apply (k : ℕ) (c : Fˣ) (M : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    twAdj k (dgHom c) M i j =
      (c : F) ^ k * (dgv (c : F) i * M i j * dgv ((c⁻¹ : Fˣ) : F) j) := by
  rw [twAdj, coe_dgHom, coe_dgHom_inv, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, smul_eq_mul]
  simp

theorem twAdj_toGL (k : ℕ) (A : SpecialLinearGroup (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    twAdj k (SpecialLinearGroup.toGL A) M = cnj (A : Matrix (Fin 3) (Fin 3) F) M := by
  rw [twAdj, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix, A.prop, one_pow, one_smul]
  rfl

section Dg

variable (k : ℕ) (c : Fˣ) {M : Matrix (Fin 3) (Fin 3) F}

theorem dgv_inv (i : Fin 3) : dgv (c : F) i * dgv ((c⁻¹ : Fˣ) : F) i = 1 := by
  rw [dgv_mul_dgv, Units.mul_inv]
  fin_cases i <;> simp

theorem twAdj_dg_diag (i : Fin 3) : twAdj k (dgHom c) M i i = (c : F) ^ k * M i i := by
  rw [twAdj_dg_apply, mul_comm (dgv (c : F) i), mul_assoc, dgv_inv, mul_one]

theorem twAdj_dg_trace : (twAdj k (dgHom c) M).trace = (c : F) ^ k * M.trace := by
  rw [Matrix.trace_fin_three, Matrix.trace_fin_three, twAdj_dg_diag, twAdj_dg_diag,
    twAdj_dg_diag]
  ring

theorem kp_dg : kp (twAdj k (dgHom c) M) = ((c : F) ^ k * c) • kp M := by
  funext i
  fin_cases i <;> simp [kp, twAdj_dg_apply, mul_assoc]

theorem km_dg : km (twAdj k (dgHom c) M) = ((c : F) ^ k * ((c⁻¹ : Fˣ) : F)) • km M := by
  funext i
  fin_cases i <;> simp [km, twAdj_dg_apply] <;> ring

theorem k2_dg : k2 (twAdj k (dgHom c) M) = ((c : F) ^ k) ^ 2 • k2 M := by
  funext i
  fin_cases i <;> simp [k2, twAdj_dg_apply] <;> ring

theorem Wp_dg (hM : M ∈ (Wp : AddSubgroup _)) :
    twAdj k (dgHom c) M ∈ (Wp : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  intro i j hij
  rw [twAdj_dg_apply, (hM : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0) i j hij]
  ring

theorem W2_dg (hM : M ∈ (W2 : AddSubgroup _)) :
    twAdj k (dgHom c) M ∈ (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [twAdj_dg_apply, h1, h2, h3, h4, h5, h6]

theorem W3_dg (hM : M ∈ (W3 : AddSubgroup _)) :
    twAdj k (dgHom c) M ∈ (W3 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [twAdj_dg_apply, h1, h2, h3, h4]

theorem W4_dg (hM : M ∈ (W4 : AddSubgroup _)) :
    twAdj k (dgHom c) M ∈ (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · rw [twAdj_dg_trace, h1, mul_zero]
  · simp [twAdj_dg_apply, h2]
  · simp [twAdj_dg_apply, h3]

theorem Wsl_dg (hM : M ∈ (Wsl : AddSubgroup _)) :
    twAdj k (dgHom c) M ∈ (Wsl : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  show (twAdj k (dgHom c) M).trace = 0
  rw [twAdj_dg_trace, show M.trace = 0 from hM, mul_zero]

variable [CharP F 2]

theorem W2a_dg (hM : M ∈ (W2a : AddSubgroup _)) :
    twAdj 0 (dgHom c) M ∈ (W2a : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  refine ⟨W2_dg 0 c hM.1, ?_⟩
  rw [twAdj_dg_diag, pow_zero, one_mul]
  exact hM.2

theorem W4a_dg (hM : M ∈ (W4a : AddSubgroup _)) :
    twAdj 0 (dgHom c) M ∈ (W4a : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  refine ⟨W4_dg 0 c hM.1, ?_⟩
  rw [twAdj_dg_diag, pow_zero, one_mul]
  exact hM.2

end Dg

end CFSG.Quasithin.H13.Ch4.B414.M
