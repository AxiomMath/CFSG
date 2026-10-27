module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Model
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.Open CFSG.SeitzReduction.OmegaPilot CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups Matrix

@[expose] noncomputable def genGL {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    GL (Fin 6 ⊕ Fin 6) (ZMod 2) :=
  flipGL (ZMod 2) P * ((leviEmbedSL (ZMod 2) 6 (Matrix.SpecialLinearGroup.transvection hab 1) :
    StatedSp 6 (ZMod 2)) : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) * (flipGL (ZMod 2) P)⁻¹

@[expose] def genMat (a b : Fin 6) (P : Finset (Fin 6)) :
    Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2) :=
  Matrix.of fun x y => Matrix.fromBlocks (Matrix.transvection a b (1 : ZMod 2)) 0 0
    (Matrix.transvection a b (1 : ZMod 2))ᵀ (flipPermFun P x) (flipPermFun P y)

private theorem transvection_inv {a b : Fin 6} (hab : a ≠ b) :
    (Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2))⁻¹ =
      Matrix.SpecialLinearGroup.transvection hab 1 := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.coe_one]
  have hS : Matrix.single a b (1 : ZMod 2) * Matrix.single a b 1 = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab) _
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hS, add_zero, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

theorem coe_genGL {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    ((genGL hab P : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) =
      genMat a b P := by
  ext x y
  rw [genGL, flipGL_conj_apply]
  have h := mat_leviEmbedSL (K := ZMod 2) (n := 6) (Matrix.SpecialLinearGroup.transvection hab 1)
  rw [transvection_inv] at h
  change mat 6 (ZMod 2) _ (flipPerm P x) (flipPerm P y) = _
  rw [h]
  rfl

private theorem closure_transvections {a b : Fin 6} (hab : a ≠ b) :
    CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := ZMod 2) ({a, b} : Finset (Fin 6)) =
      Subgroup.closure {Matrix.SpecialLinearGroup.transvection hab 1,
        Matrix.SpecialLinearGroup.transvection hab.symm 1} := by
  rw [CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_eq_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · have : Matrix.SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 := by
        ext k l
        simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection_zero]
      rw [this]
      exact one_mem _
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hij
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact absurd rfl hij
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure ⟨a, b, hab, 1, by simp, by simp, rfl⟩
    · exact Subgroup.subset_closure ⟨b, a, hab.symm, 1, by simp, by simp, rfl⟩

theorem rootL_eq_closure {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    rootL {a, b} P = Subgroup.closure {lin (genGL hab P), lin (genGL hab.symm P)} := by
  rw [rootL, siegelBlockGL, CFSG.SeitzReduction.SymplecticPilot.siegelBlock, closure_transvections hab]
  simp only [MonoidHom.map_closure, Set.image_pair]
  rfl

end CFSG.StandardType.FrameRoute.FS81.D6M
