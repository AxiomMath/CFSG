module

public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.Sign

public section

namespace CFSG.Sporadic.Suz

open CFSG.F3.Native Native Matrix CFSG.Sporadic.VecOrbit

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev mF : Matrix (Fin 64) (Fin 64) (ZMod 3) := toMat 64 formF

noncomputable abbrev mP : Matrix (Fin 64) (Fin 64) (ZMod 3) := toMat 64 formP

noncomputable abbrev mPinv : Matrix (Fin 64) (Fin 64) (ZMod 3) := toMat 64 formPinv

@[expose] def dvec : Fin 64 → ZMod 3 := fun i => (formD[i.val]! : ZMod 3)

theorem formChecks_parts :
    RowsWF formF ∧ RowsWF formP ∧ RowsWF formPinv ∧ formF.size = 64 ∧
    formP.size = 64 ∧ formPinv.size = 64 ∧
    eqM 64 (mul 64 (transpose 64 matA) (mul 64 formF matA)) formF = true ∧
    eqM 64 (mul 64 (transpose 64 matB) (mul 64 formF matB)) formF = true ∧
    eqM 64 (mul 64 (transpose 64 formP) (mul 64 formF formP)) diagD = true ∧
    eqM 64 (mul 64 formPinv formP) (idM 64) = true := by
  have h := certificate_parts.2.1
  unfold formChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨rowsWF_of_wfM h1, rowsWF_of_wfM h2, rowsWF_of_wfM h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem transpose_size (d : ℕ) (X : Array V) : (CFSG.F3.Native.transpose d X).size = d := by
  unfold CFSG.F3.Native.transpose; simp

theorem toMat_conj_form {X : Array V} (hX : RowsWF X) :
    toMat 64 (mul 64 (transpose 64 X) (mul 64 formF X)) = (toMat 64 X)ᵀ * mF * toMat 64 X := by
  obtain ⟨hF, -, -, hFs, -⟩ := formChecks_parts
  rw [toMat_mul (transpose_size 64 X) (RowsWF.transpose 64 X) (RowsWF.mul _ 64 hF hX),
    toMat_transpose, toMat_mul hFs hF hX, mul_assoc]

theorem A_form : mAᵀ * mF * mA = mF := by
  have := toMat_eq_of_eqM formChecks_parts.2.2.2.2.2.2.1
  rwa [toMat_conj_form rowsWF_matA, toMat_matA] at this

theorem B_form : mBᵀ * mF * mB = mF := by
  have := toMat_eq_of_eqM formChecks_parts.2.2.2.2.2.2.2.1
  rwa [toMat_conj_form rowsWF_matB, toMat_matB] at this

theorem toMat_diagD : toMat 64 diagD = Matrix.diagonal dvec := by
  ext i j
  rw [toMat_apply, Matrix.diagonal_apply]
  unfold diagD
  rw [getElem!_pos _ i.val (by simp), Array.getElem_ofFn, V.val_ofFn, ite_eq_left j.isLt]
  by_cases h : i = j
  · subst h; simp [dvec]
  · have : j.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, this]

theorem P_form : mPᵀ * mF * mP = Matrix.diagonal dvec := by
  obtain ⟨-, hP, -, -, -, -, -, -, h9, -⟩ := formChecks_parts
  have := toMat_eq_of_eqM h9
  rwa [toMat_conj_form hP, toMat_diagD] at this

theorem Pinv_P : mPinv * mP = 1 := by
  obtain ⟨-, hP, hPi, -, -, hPis, -, -, -, h10⟩ := formChecks_parts
  have := toMat_eq_of_eqM h10
  rwa [toMat_mul hPis hPi hP, toMat_idM] at this

theorem J_form :
    ∀ g ∈ J, ((g : Matrix (Fin 64) (Fin 64) (ZMod 3)))ᵀ * mF * g = mF := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact A_form
    · exact B_form
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (↑y)ᵀ * (↑x)ᵀ * mF * (↑x * ↑y) = (↑y)ᵀ * ((↑x)ᵀ * mF * ↑x) * ↑y := by
          simp only [mul_assoc]
      _ = mF := by rw [hx, hy]
  | inv x _ hx =>
    have h2 : (x : Matrix (Fin 64) (Fin 64) (ZMod 3)) *
        ((x⁻¹ : GL (Fin 64) (ZMod 3)) : Matrix (Fin 64) (Fin 64) (ZMod 3)) = 1 := Units.mul_inv x
    set y : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
      ((x⁻¹ : GL (Fin 64) (ZMod 3)) : Matrix (Fin 64) (Fin 64) (ZMod 3))
    set z : Matrix (Fin 64) (Fin 64) (ZMod 3) := (x : Matrix (Fin 64) (Fin 64) (ZMod 3))
    calc yᵀ * mF * y = yᵀ * (zᵀ * mF * z) * y := by rw [hx]
      _ = (z * y)ᵀ * mF * (z * y) := by rw [Matrix.transpose_mul]; simp only [mul_assoc]
      _ = mF := by rw [h2, Matrix.transpose_one, one_mul, mul_one]

set_option maxRecDepth 100000 in
theorem cnt_eval : triAt (cnt3 (List.ofFn fun i : Fin 64 => 2 * dvec i)) 1 = 3 ^ 63 + 3 ^ 31 := by
  decide

theorem card_lev : Fintype.card (Lev mF) = 3 ^ 63 + 3 ^ 31 := by
  rw [card_lev_eq_diag mF mP mPinv dvec Pinv_P P_form, card_diag, cnt_eval]

theorem mat_ne_neg_one (g : J) : mat g ≠ -1 :=
  ne_neg_one_of_sign mF J J_form closure_ab b_cube ab_pow (by rw [card_lev]; norm_num) g

end CFSG.Sporadic.Suz
