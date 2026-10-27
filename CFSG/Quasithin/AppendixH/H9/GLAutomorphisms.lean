module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.Quasithin.AppendixH.H9.GL.DualNotInner
import CFSG.Quasithin.AppendixH.H9.GL.ProjectiveEquiv

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ}

theorem exists_aut_form_GL_two (hn : 3 ≤ n) (α : MulAut (GL (Fin n) (ZMod 2))) :
    ∃ B : GL (Fin n) (ZMod 2),
      (∀ X, α X = B * X * B⁻¹) ∨ (∀ X, α X = B * dualGLn n X * B⁻¹) := by
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := ZMod 2) (n := n) hn
  obtain ⟨A, σ, ε, hε, hβ⟩ := hgen (((GL.glEquivProj n).symm.trans α).trans (GL.glEquivProj n))
  have hσ : σ = 1 := Subsingleton.elim σ 1
  have key : ∀ X, α X = (GL.glEquivProj n).symm
      ((((GL.glEquivProj n).symm.trans α).trans (GL.glEquivProj n))
        (GL.glEquivProj n X)) := by
    intro X
    simp
  refine ⟨A, ?_⟩
  interval_cases ε
  · left
    intro X
    rw [key, hβ, hσ, map_one, pow_zero, mul_one, mul_one, GL.glEquivProj_symm_conjAut]
  · right
    intro X
    rw [key, hβ, hσ, map_one, pow_one, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
    apply Units.ext
    rw [GL.coe_glEquivProj_symm_conjAut_dualAut, Units.val_mul, Units.val_mul]
    rfl

theorem dualGLn_not_inner (hn : 3 ≤ n) :
    ¬ ∃ B : GL (Fin n) (ZMod 2), ∀ X : GL (Fin n) (ZMod 2), dualGLn n X = B * X * B⁻¹ :=
  GL.dualGLn_not_inner_aux hn

end CFSG.ASVolI.ChH
