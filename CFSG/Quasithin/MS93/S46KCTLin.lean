module

public import CFSG.Quasithin.MS93.S468Red
public import CFSG.Quasithin.MS93.S46KC2Lin

public section

namespace CFSG.Quasithin.MS93.S46.KCT

open CFSG.Quasithin.MS93.S468
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem coe_rootElt_mul_rootElt (a b : F) :
    ((rootElt 1 0 a * rootElt 2 0 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      1 + Matrix.vecMulVec ![0, a, b] (Pi.single 0 1) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootElt (show (1 : Fin 3) ≠ 0 by decide),
    coe_rootElt (show (2 : Fin 3) ≠ 0 by decide)]
  ext i j
  rw [Matrix.add_apply (1 : Matrix (Fin 3) (Fin 3) F), Matrix.vecMulVec_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

theorem coe_conj_rootElt_mul_rootElt (P : SL3 F) (h : Fin 3 → F) (h0 : h 0 = 0) :
    ((P * (rootElt 1 0 (h 1) * rootElt 2 0 (h 2)) * P⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      1 + Matrix.vecMulVec ((P : Matrix (Fin 3) (Fin 3) F) *ᵥ h)
        (((P⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0) := by
  have hh : (![0, h 1, h 2] : Fin 3 → F) = h := by
    funext i
    fin_cases i <;> simp [h0]
  have hP : (P : Matrix (Fin 3) (Fin 3) F) * ((P⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_rootElt_mul_rootElt, hh, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hP,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 2
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem mem_stabX0_of_coe {A : SL3 F} {f : Fin 3 → F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec ![0, f 2, f 1] f) :
    A ∈ (stabX0 : Subgroup (SL3 F)) := by
  intro v
  rw [hA, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Matrix.vecMulVec_mulVec]
  simp

theorem rootElt_two_one_mem_stabX0 (c : F) : rootElt 2 1 c ∈ (stabX0 : Subgroup (SL3 F)) := by
  intro v
  rw [coe_rootElt (show (2 : Fin 3) ≠ 1 by decide)]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem eq_zero_or_eq_one [CharP F 2] [Fintype F] (hq : Fintype.card F = 2) (a : F) :
    a = 0 ∨ a = 1 := by
  obtain ⟨x, hx⟩ := KC2.exists_embv_eq hq (fun _ => a)
  have ha : a = KC2.iota F (x 0) := (congrFun hx 0).symm
  rw [ha]
  generalize x 0 = y
  fin_cases y
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

theorem cube_mem [CharP F 2] [Fintype F] (hq : Fintype.card F = 2) {A : SL3 F} {f : Fin 3 → F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec ![0, f 2, f 1] f)
    (hf : ¬ (f 1 = 0 ∧ f 2 = 0)) :
    (A⁻¹ * rootElt 2 1 1) ^ 3 ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) := by
  set X : ↥(stabX0 : Subgroup (SL3 F)) :=
    (⟨A, mem_stabX0_of_coe hA⟩ : ↥(stabX0 : Subgroup (SL3 F)))⁻¹ *
      ⟨rootElt 2 1 1, rootElt_two_one_mem_stabX0 1⟩ with hX
  have e : (A⁻¹ * rootElt 2 1 1) ^ 3 = ((X ^ 3 : ↥(stabX0 : Subgroup (SL3 F))) : SL3 F) := by
    rw [hX]
    simp
  rw [e]
  refine mem_rootGroup_sup_of_blockHom_eq_one ?_
  rw [map_pow, hX, map_mul, map_inv]
  set S := blockHom (⟨A, mem_stabX0_of_coe hA⟩ : ↥(stabX0 : Subgroup (SL3 F))) with hS
  set R := blockHom (⟨rootElt 2 1 1, rootElt_two_one_mem_stabX0 1⟩ :
    ↥(stabX0 : Subgroup (SL3 F))) with hR
  have hSm : (S : Matrix (Fin 2) (Fin 2) F) =
      !![1 + f 2 * f 1, f 2 * f 2; f 1 * f 1, 1 + f 1 * f 2] := by
    ext i j
    rw [hS, blockHom_apply, hA, Matrix.add_apply, Matrix.vecMulVec_apply]
    fin_cases i <;> fin_cases j <;> simp
  have hRm : (R : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := by
    ext i j
    rw [hR, blockHom_apply, coe_rootElt (show (2 : Fin 3) ≠ 1 by decide)]
    fin_cases i <;> fin_cases j <;> simp
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hSm, hRm, Matrix.adjugate_fin_two_of,
    Matrix.SpecialLinearGroup.coe_one]
  rcases eq_zero_or_eq_one hq (f 1) with h1 | h1 <;>
    rcases eq_zero_or_eq_one hq (f 2) with h2 | h2
  · exact absurd ⟨h1, h2⟩ hf
  all_goals
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq,
        CharTwo.add_self_eq_zero]

end CFSG.Quasithin.MS93.S46.KCT
