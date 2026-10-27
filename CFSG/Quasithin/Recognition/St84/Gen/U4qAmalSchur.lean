module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLineDefs

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem mul_mul_map_bar_transpose_apply (A X : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (A * X * (A.map h.bar)ᵀ) i j =
      A i 0 * X 0 0 * h.bar (A j 0) + A i 0 * X 0 1 * h.bar (A j 1) +
        A i 1 * X 1 0 * h.bar (A j 0) + A i 1 * X 1 1 * h.bar (A j 1) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply]
  ring

private def u4SchurE₁ : ↥(u4Herm h) :=
  ⟨!![1, 0; 0, 0], (mem_u4Herm h).mpr fun i j => by fin_cases i <;> fin_cases j <;> simp⟩

private def u4SchurE₂ : ↥(u4Herm h) :=
  ⟨!![0, 0; 0, 1], (mem_u4Herm h).mpr fun i j => by fin_cases i <;> fin_cases j <;> simp⟩

private noncomputable def u4SchurM (s : K) : ↥(u4Herm h) :=
  ⟨!![0, s; h.bar s, 0], (mem_u4Herm h).mpr fun i j => by
    fin_cases i <;> fin_cases j <;> simp [h.bar_bar]⟩

private noncomputable def u4SchurN (s : K) : h.fixedField :=
  ⟨s * h.bar s, by rw [h.mem_fixedField, map_mul, h.bar_bar, mul_comm]⟩

private def u4SchurU (s : K) : SL(2, K) :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

private def u4SchurD {μ : K} (hμ : μ ≠ 0) : SL(2, K) :=
  ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two, hμ]⟩

private def u4SchurW : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by
    haveI := h.charP
    simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private theorem coe_u4SchurU (s : K) :
    ((u4SchurU s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, s; 0, 1] :=
  rfl

private theorem coe_u4SchurD {μ : K} (hμ : μ ≠ 0) :
    ((u4SchurD hμ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![μ, 0; 0, μ⁻¹] :=
  rfl

private theorem coe_u4SchurW :
    ((u4SchurW h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

private theorem u4Schur_twist_U_E₁ (s : K) :
    u4TwistLin h ((u4SchurU s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (u4SchurE₁ h) =
      u4SchurE₁ h := by
  apply Subtype.ext
  ext i j
  rw [coe_u4TwistLin, coe_u4SchurU, mul_mul_map_bar_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [u4SchurE₁]

private theorem u4Schur_twist_D_E₁ {x : h.fixedField} {μ : K} (hμ : μ ≠ 0)
    (hμf : h.bar μ = μ) (hx : (x : K) = μ * μ) :
    u4TwistLin h ((u4SchurD hμ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (u4SchurE₁ h) =
      x • u4SchurE₁ h := by
  apply Subtype.ext
  ext i j
  rw [coe_u4TwistLin, coe_u4SchurD, mul_mul_map_bar_transpose_apply, Submodule.coe_smul,
    Matrix.smul_apply, Subfield.smul_def, hx]
  fin_cases i <;> fin_cases j <;> simp [u4SchurE₁, hμf]

private theorem u4Schur_twist_W_E₁ :
    u4TwistLin h ((u4SchurW h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (u4SchurE₁ h) =
      u4SchurE₂ h := by
  apply Subtype.ext
  ext i j
  rw [coe_u4TwistLin, coe_u4SchurW, mul_mul_map_bar_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [u4SchurE₁, u4SchurE₂]

private theorem u4Schur_twist_U_E₂ (s : K) :
    u4TwistLin h ((u4SchurU s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (u4SchurE₂ h) =
      u4SchurN h s • u4SchurE₁ h + u4SchurE₂ h + u4SchurM h s := by
  apply Subtype.ext
  ext i j
  rw [coe_u4TwistLin, coe_u4SchurU, mul_mul_map_bar_transpose_apply, Submodule.coe_add,
    Submodule.coe_add, Submodule.coe_smul, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
    Subfield.smul_def]
  fin_cases i <;> fin_cases j <;> simp [u4SchurE₁, u4SchurE₂, u4SchurM, u4SchurN]

private theorem u4Schur_eq_smul_E₁ (Y : ↥(u4Herm h))
    (hY : ∀ s : K,
      u4TwistLin h ((u4SchurU s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) Y = Y) :
    Y = (⟨(Y : Matrix (Fin 2) (Fin 2) K) 0 0,
      (h.mem_fixedField).mpr ((mem_u4Herm h).mp Y.2 0 0)⟩ : h.fixedField) • u4SchurE₁ h := by
  have hY' : ∀ (s : K) (i j : Fin 2),
      ((u4TwistLin h ((u4SchurU s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) Y : ↥(u4Herm h)) :
        Matrix (Fin 2) (Fin 2) K) i j = (Y : Matrix (Fin 2) (Fin 2) K) i j :=
    fun s i j => by rw [hY s]
  have e1 := hY' 1 0 1
  have e2 := hY' 1 0 0
  have e3 := hY' (u4Omega h) 0 0
  rw [coe_u4TwistLin, coe_u4SchurU, mul_mul_map_bar_transpose_apply] at e1 e2 e3
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, map_one, map_zero, one_mul,
    mul_one, mul_zero, zero_mul, add_zero, zero_add] at e1 e2 e3
  have h11 : (Y : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by linear_combination e1
  have h01' : (Y : Matrix (Fin 2) (Fin 2) K) 0 1 * (h.bar (u4Omega h) - u4Omega h) = 0 := by
    linear_combination e3 - u4Omega h * e2 -
      (u4Omega h * h.bar (u4Omega h) - u4Omega h) * h11
  have h01 : (Y : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 :=
    (mul_eq_zero.mp h01').resolve_right (sub_ne_zero.mpr (bar_u4Omega_ne h))
  have h10 : (Y : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [← (mem_u4Herm h).mp Y.2 0 1, h01, map_zero]
  apply Subtype.ext
  ext i j
  rw [Submodule.coe_smul, Matrix.smul_apply, Subfield.smul_def]
  fin_cases i <;> fin_cases j <;> simp [u4SchurE₁, h01, h10, h11]

private theorem u4Schur_decomp (X : ↥(u4Herm h)) :
    X = (⟨(X : Matrix (Fin 2) (Fin 2) K) 0 0,
        (h.mem_fixedField).mpr ((mem_u4Herm h).mp X.2 0 0)⟩ : h.fixedField) • u4SchurE₁ h +
      (⟨(X : Matrix (Fin 2) (Fin 2) K) 1 1,
        (h.mem_fixedField).mpr ((mem_u4Herm h).mp X.2 1 1)⟩ : h.fixedField) • u4SchurE₂ h +
      u4SchurM h ((X : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have h10 := (mem_u4Herm h).mp X.2 0 1
  apply Subtype.ext
  ext i j
  rw [Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Subfield.smul_def,
    Subfield.smul_def]
  fin_cases i <;> fin_cases j <;> simp [u4SchurE₁, u4SchurE₂, u4SchurM, h10]

theorem exists_smul_of_comm_u4TwistLin (T : ↥(u4Herm h) →+ ↥(u4Herm h))
    (hT : ∀ (A : SL(2, K)) (X : ↥(u4Herm h)),
      T (u4TwistLin h (A : Matrix (Fin 2) (Fin 2) K) X) =
        u4TwistLin h (A : Matrix (Fin 2) (Fin 2) K) (T X)) :
    ∃ c : h.fixedField, ∀ X, T X = c • X := by
  haveI := h.charP
  haveI := h.finite
  have hfix : ∀ s : K, u4TwistLin h ((u4SchurU s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
      (T (u4SchurE₁ h)) = T (u4SchurE₁ h) := by
    intro s
    rw [← hT, u4Schur_twist_U_E₁]
  obtain ⟨c, hc⟩ : ∃ c : h.fixedField, T (u4SchurE₁ h) = c • u4SchurE₁ h :=
    ⟨_, u4Schur_eq_smul_E₁ h _ hfix⟩
  have h2 : ∀ x : h.fixedField, T (x • u4SchurE₁ h) = c • x • u4SchurE₁ h := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [zero_smul, map_zero, smul_zero]
    obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (x : K)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      apply hx
      exact Subtype.ext (by rw [hμ, mul_zero]; rfl)
    have hμf : h.bar μ = μ := by
      have hxf : h.bar (x : K) = x := (h.mem_fixedField).mp x.2
      rw [hμ, map_mul] at hxf
      exact CharTwo.sq_inj.mp (by rw [sq, sq]; exact hxf)
    rw [← u4Schur_twist_D_E₁ h hμ0 hμf hμ, hT, hc, map_smul]
  have h3 : ∀ x : h.fixedField, T (x • u4SchurE₂ h) = c • x • u4SchurE₂ h := by
    intro x
    rw [← u4Schur_twist_W_E₁ h, ← map_smul, hT, h2, map_smul, map_smul]
  have hE₂ : T (u4SchurE₂ h) = c • u4SchurE₂ h := by
    simpa only [one_smul] using h3 1
  have h4 : ∀ s : K, T (u4SchurM h s) = c • u4SchurM h s := by
    intro s
    have e := hT (u4SchurU s) (u4SchurE₂ h)
    rw [u4Schur_twist_U_E₂, map_add, map_add, h2, hE₂, map_smul, u4Schur_twist_U_E₂, smul_add,
      smul_add] at e
    exact add_left_cancel e
  refine ⟨c, fun X => ?_⟩
  rw [u4Schur_decomp h X, map_add, map_add, h2, h3, h4, smul_add, smul_add]

end CFSG.Quasithin.F112R.St84

end
