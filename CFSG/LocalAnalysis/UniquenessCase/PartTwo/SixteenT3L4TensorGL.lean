module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dimension.DivisionRing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Matrix

private theorem s16t_l4g_extend_pair {a b : Fin 4 → ZMod 2}
    (h : LinearIndependent (ZMod 2) ![a, b]) :
    ∃ c d : Fin 4 → ZMod 2, LinearIndependent (ZMod 2) ![a, b, c, d] := by
  obtain ⟨c, hc⟩ := exists_linearIndependent_snoc_of_lt_finrank (v := ![a, b]) h (by simp)
  have hc' : LinearIndependent (ZMod 2) ![a, b, c] := by
    convert hc using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨d, hd⟩ := exists_linearIndependent_snoc_of_lt_finrank (v := ![a, b, c]) hc' (by simp)
  refine ⟨c, d, ?_⟩
  convert hd using 1
  funext i
  fin_cases i <;> rfl

private theorem s16t_l4g_exists_gl4 {v : Fin 4 → Fin 4 → ZMod 2}
    (h : LinearIndependent (ZMod 2) v) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
      ∀ j, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single j 1) = v j := by
  let A : Matrix (Fin 4) (Fin 4) (ZMod 2) := Matrix.of fun i j => v j i
  have hcol : A.col = v := by
    funext j i
    rfl
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact h
  refine ⟨hA.unit, fun j => ?_⟩
  rw [show ((hA.unit : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = A from IsUnit.unit_spec hA, Matrix.mulVec_single_one]
  exact congrFun hcol j

private def s16t_l4g_g0 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def s16t_l4g_k0 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

private theorem s16t_l4g_g0_cube : s16t_l4g_g0 * (s16t_l4g_g0 * s16t_l4g_g0) = 1 := by
  decide

private theorem s16t_l4g_g0_cube' : s16t_l4g_g0 * s16t_l4g_g0 * s16t_l4g_g0 = 1 := by
  decide

private theorem s16t_l4g_k0_cube : s16t_l4g_k0 * (s16t_l4g_k0 * s16t_l4g_k0) = 1 := by
  decide

private theorem s16t_l4g_k0_cube' : s16t_l4g_k0 * s16t_l4g_k0 * s16t_l4g_k0 = 1 := by
  decide

private theorem s16t_l4g_g0_comm : s16t_l4g_g0 * s16t_l4g_k0 = s16t_l4g_k0 * s16t_l4g_g0 := by
  decide

private def s16t_l4g_gU : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
  ⟨s16t_l4g_g0, s16t_l4g_g0 * s16t_l4g_g0, s16t_l4g_g0_cube, s16t_l4g_g0_cube'⟩

private def s16t_l4g_kU : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
  ⟨s16t_l4g_k0, s16t_l4g_k0 * s16t_l4g_k0, s16t_l4g_k0_cube, s16t_l4g_k0_cube'⟩

private theorem s16t_l4g_gU_pow : s16t_l4g_gU ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  decide

private theorem s16t_l4g_kU_pow : s16t_l4g_kU ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  decide

private theorem s16t_l4g_kU_ne_one : s16t_l4g_kU ≠ 1 := by
  intro h
  have h1 : s16t_l4g_k0 = 1 := congrArg Units.val h
  revert h1
  decide

private theorem s16t_l4g_gU_comm : s16t_l4g_gU * s16t_l4g_kU = s16t_l4g_kU * s16t_l4g_gU :=
  Units.ext s16t_l4g_g0_comm

private theorem s16t_l4g_g0_apply :
    s16t_l4g_g0.mulVec (Pi.single 0 1) = Pi.single 0 1 + Pi.single 1 1 ∧
      s16t_l4g_g0.mulVec (Pi.single 1 1) = Pi.single 0 1 := by
  decide

private theorem s16t_l4g_k0_apply :
    s16t_l4g_k0.mulVec (Pi.single 0 1) = Pi.single 0 1 ∧
      s16t_l4g_k0.mulVec (Pi.single 1 1) = Pi.single 1 1 := by
  decide

theorem s16t_l4_gl_pair_of_independent {c₁ c₂ : Fin 4 → ZMod 2}
    (h : LinearIndependent (ZMod 2) ![c₁, c₂]) :
    ∃ g k : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
      g ^ 3 = 1 ∧ k ^ 3 = 1 ∧ k ≠ 1 ∧ g * k = k * g ∧
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec c₁ = c₁ + c₂ ∧
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec c₂ = c₁ ∧
      (k : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec c₁ = c₁ ∧
      (k : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec c₂ = c₂ := by
  obtain ⟨c₃, c₄, h4⟩ := s16t_l4g_extend_pair h
  obtain ⟨u, hu⟩ := s16t_l4g_exists_gl4 h4
  have hu0 : (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1) = c₁ := hu 0
  have hu1 : (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1) = c₂ := hu 1
  have hconj : ∀ (x : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2),
      ((u * x * u⁻¹ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) =
      (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        ((x : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) := by
    intro x v
    simp [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨u * s16t_l4g_gU * u⁻¹, u * s16t_l4g_kU * u⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conj_pow, s16t_l4g_gU_pow, mul_one, mul_inv_cancel]
  · rw [conj_pow, s16t_l4g_kU_pow, mul_one, mul_inv_cancel]
  · intro h1
    apply s16t_l4g_kU_ne_one
    have h2 := congrArg (fun x => u⁻¹ * x * u) h1
    simpa [mul_assoc] using h2
  · calc u * s16t_l4g_gU * u⁻¹ * (u * s16t_l4g_kU * u⁻¹)
        = u * (s16t_l4g_gU * s16t_l4g_kU) * u⁻¹ := by group
      _ = u * (s16t_l4g_kU * s16t_l4g_gU) * u⁻¹ := by rw [s16t_l4g_gU_comm]
      _ = u * s16t_l4g_kU * u⁻¹ * (u * s16t_l4g_gU * u⁻¹) := by group
  · calc _ = ((u * s16t_l4g_gU * u⁻¹ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1)) := by rw [hu0]
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((s16t_l4g_gU : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1)) :=
        hconj _ _
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1 + Pi.single 1 1) := by
        rw [show (s16t_l4g_gU : Matrix (Fin 4) (Fin 4) (ZMod 2)) = s16t_l4g_g0 from rfl,
          s16t_l4g_g0_apply.1]
      _ = c₁ + c₂ := by rw [Matrix.mulVec_add, hu0, hu1]
  · calc _ = ((u * s16t_l4g_gU * u⁻¹ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1)) := by rw [hu1]
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((s16t_l4g_gU : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1)) :=
        hconj _ _
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1) := by
        rw [show (s16t_l4g_gU : Matrix (Fin 4) (Fin 4) (ZMod 2)) = s16t_l4g_g0 from rfl,
          s16t_l4g_g0_apply.2]
      _ = c₁ := hu0
  · calc _ = ((u * s16t_l4g_kU * u⁻¹ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1)) := by rw [hu0]
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((s16t_l4g_kU : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1)) :=
        hconj _ _
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1) := by
        rw [show (s16t_l4g_kU : Matrix (Fin 4) (Fin 4) (ZMod 2)) = s16t_l4g_k0 from rfl,
          s16t_l4g_k0_apply.1]
      _ = c₁ := hu0
  · calc _ = ((u * s16t_l4g_kU * u⁻¹ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1)) := by rw [hu1]
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
          ((s16t_l4g_kU : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1)) :=
        hconj _ _
      _ = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1) := by
        rw [show (s16t_l4g_kU : Matrix (Fin 4) (Fin 4) (ZMod 2)) = s16t_l4g_k0 from rfl,
          s16t_l4g_k0_apply.2]
      _ = c₂ := hu1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
