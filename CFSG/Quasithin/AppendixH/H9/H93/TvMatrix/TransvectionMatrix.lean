module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.GLBasics
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

variable {n : ℕ}

@[expose] def IsTvMat (A : GL (Fin n) (ZMod 2)) : Prop :=
  ∃ u f : Fin n → ZMod 2, u ≠ 0 ∧ f ≠ 0 ∧
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + Matrix.vecMulVec u f

private theorem dotProduct_eq_zero_of_val_eq {A : GL (Fin n) (ZMod 2)} {u f : Fin n → ZMod 2}
    (hA : (A : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + Matrix.vecMulVec u f) (hu : u ≠ 0) :
    f ⬝ᵥ u = 0 := by
  rcases zmod_two_cases (f ⬝ᵥ u) with h | h
  · exact h
  · exfalso
    apply hu
    apply (GL_mulVec_eq_zero_iff A u).mp
    rw [hA, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, h,
      one_smul]
    exact vec_add_self u

theorem IsTvMat.mul_self {A : GL (Fin n) (ZMod 2)} (hA : IsTvMat A) : A * A = 1 := by
  obtain ⟨u, f, hu, _, hA⟩ := hA
  apply Units.ext
  rw [Units.val_mul, hA, Units.val_one]
  exact one_add_vecMulVec_mul_self (dotProduct_eq_zero_of_val_eq hA hu)

theorem IsTvMat.inv_eq_self {A : GL (Fin n) (ZMod 2)} (hA : IsTvMat A) : A⁻¹ = A :=
  inv_eq_of_mul_eq_one_right hA.mul_self

theorem IsTvMat.dualGLn {A : GL (Fin n) (ZMod 2)} (hA : IsTvMat A) : IsTvMat (dualGLn n A) := by
  obtain ⟨u, f, hu, hf, hA'⟩ := id hA
  refine ⟨f, u, hf, hu, ?_⟩
  rw [dualGLn_val, hA.inv_eq_self, hA', Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]

private theorem conj_one_add_vecMulVec (B : GL (Fin n) (ZMod 2)) (u f : Fin n → ZMod 2) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (1 + Matrix.vecMulVec u f) *
        ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      1 + Matrix.vecMulVec ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u)
        (f ᵥ* ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem IsTvMat.conj {A : GL (Fin n) (ZMod 2)} (hA : IsTvMat A) (B : GL (Fin n) (ZMod 2)) :
    IsTvMat (B * A * B⁻¹) := by
  obtain ⟨u, f, hu, hf, hA⟩ := hA
  refine ⟨(B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u,
    f ᵥ* ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)), ?_, ?_, ?_⟩
  · intro h
    exact hu ((GL_mulVec_eq_zero_iff B u).mp h)
  · intro h
    apply hf
    have h1 := congrArg (fun v => v ᵥ* (B : Matrix (Fin n) (Fin n) (ZMod 2))) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using h1
  · rw [Units.val_mul, Units.val_mul, hA]
    exact conj_one_add_vecMulVec B u f

theorem IsTvMat.ne_one {A : GL (Fin n) (ZMod 2)} (hA : IsTvMat A) : A ≠ 1 := by
  obtain ⟨u, f, hu, hf, hAv⟩ := hA
  intro h1
  rw [h1, Units.val_one] at hAv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hf
  have h2 := congrFun (congrFun hAv i) j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply] at h2
  have hu1 : u i = 1 := (zmod_two_cases (u i)).resolve_left hi
  have hf1 : f j = 1 := (zmod_two_cases (f j)).resolve_left hj
  rw [hu1, hf1, mul_one] at h2
  generalize (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j = c at h2
  revert c
  decide

theorem IsTvMat.exists_conj {A A' : GL (Fin n) (ZMod 2)} (hA : IsTvMat A) (hA' : IsTvMat A') :
    ∃ C : GL (Fin n) (ZMod 2), C * A * C⁻¹ = A' := by
  obtain ⟨u, f, hu, hf, hAv⟩ := hA
  obtain ⟨u', f', hu', hf', hAv'⟩ := hA'
  have h0 := dotProduct_eq_zero_of_val_eq hAv hu
  have h0' := dotProduct_eq_zero_of_val_eq hAv' hu'
  obtain ⟨C, hCu, hCf⟩ := exists_GL_mulVec_pair hu hf hu' hf' (h0.trans h0'.symm)
  refine ⟨C, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, hAv, hAv', conj_one_add_vecMulVec, hCu]
  congr 2
  rw [← hCf, dualGLn_val, Matrix.mulVec_transpose]

theorem isTvMat_transvectionGL {u f : Fin n → ZMod 2} (hu : u ≠ 0) (hf : f ≠ 0)
    (h : f ⬝ᵥ u = 0) : IsTvMat (transvectionGL u f h) :=
  ⟨u, f, hu, hf, rfl⟩

theorem IsTvMat.exists_eq_transvectionGL {A : GL (Fin n) (ZMod 2)} (hA : IsTvMat A) :
    ∃ (u f : Fin n → ZMod 2) (h : f ⬝ᵥ u = 0), u ≠ 0 ∧ f ≠ 0 ∧ A = transvectionGL u f h := by
  obtain ⟨u, f, hu, hf, hAv⟩ := hA
  exact ⟨u, f, dotProduct_eq_zero_of_val_eq hAv hu, hu, hf, Units.ext hAv⟩

end CFSG.ASVolI.ChH
