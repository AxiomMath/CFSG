module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs
import CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof (finrank_bounds)
open CFSG.RankThree.PartTwo.KFacts.KS116Proof (uu uu_add uu_zero uu_injective)
open scoped MatrixGroups

namespace L38Faithful

section Levi

variable (F : Type) [Field F]

@[expose] def blockM (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

variable {F}

theorem blockM_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    blockM F (A * B) = blockM F A * blockM F B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockM, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blockM_one : blockM F (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockM]

theorem det_blockM (A : Matrix (Fin 2) (Fin 2) F) : (blockM F A).det = A.det := by
  simp [blockM, Matrix.det_fin_three, Matrix.det_fin_two]

variable (F)

@[expose] noncomputable def blockSL : SL(2, F) →* SL(3, F) where
  toFun A := ⟨blockM F (A : Matrix (Fin 2) (Fin 2) F), by rw [det_blockM]; exact A.2⟩
  map_one' := Subtype.ext (by simp [blockM_one])
  map_mul' A B := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact blockM_mul _ _)

theorem coe_blockSL (A : SL(2, F)) :
    ((blockSL F A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      blockM F (A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem projSL_eq_range :
    projSL 3 F =
      (Matrix.SpecialLinearGroup.toPGL : SL(3, F) →* Matrix.ProjGenLinGroup (Fin 3) F).range := by
  rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
    Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

@[expose] noncomputable def levi : SL(2, F) →* projSL 3 F :=
  ((Matrix.SpecialLinearGroup.toPGL : SL(3, F) →* Matrix.ProjGenLinGroup (Fin 3) F).comp
    (blockSL F)).codRestrict (projSL 3 F) (fun A => by
      rw [projSL_eq_range]
      exact ⟨blockSL F A, rfl⟩)

theorem levi_injective : Function.Injective (levi F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have h : blockSL F A ∈ (Matrix.SpecialLinearGroup.toPGL :
      SL(3, F) →* Matrix.ProjGenLinGroup (Fin 3) F).ker := by
    rw [MonoidHom.mem_ker] at hA ⊢
    exact congrArg Subtype.val hA
  rw [Matrix.SpecialLinearGroup.toPGL_ker, Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have e : ∀ i j : Fin 3, (Matrix.scalar (Fin 3) r) i j =
      ((blockSL F A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) i j := fun i j => by rw [hr]
  have h22 := e 2 2
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp [coe_blockSL, blockM, Matrix.scalar_apply] at h22 h00 h01 h10 h11
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← h22, ← h00, ← h01, ← h10, ← h11]

end Levi

end L38Faithful

theorem l38FaithfulFix_holds : SimsR1L38FaithfulFix := by
  intro r _ hr V _ _ _ ρ hρ
  have hK : (2 : ZMod r) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have hcard : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  obtain ⟨-, hX⟩ := finrank_bounds hK (ρ.comp (L38Faithful.levi (GaloisField 2 3)))
    (hρ.comp (L38Faithful.levi_injective _))
  have hu2 : uu (1 : GaloisField 2 3) * uu 1 = 1 := by
    rw [← uu_add, CharTwo.add_self_eq_zero, uu_zero]
  have hu1 : uu (1 : GaloisField 2 3) ≠ 1 := fun h =>
    one_ne_zero (uu_injective (h.trans uu_zero.symm))
  refine ⟨L38Faithful.levi _ (uu 1), orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [pow_two, ← map_mul, hu2, map_one]
  · intro h
    exact hu1 (L38Faithful.levi_injective _ (h.trans (map_one _).symm))
  · have h := hX (uu 1) hu2 hu1
    rw [hcard] at h
    exact le_trans (by norm_num) h

end CFSG.RankThree.PartTwo.Sec11.SimsR1
