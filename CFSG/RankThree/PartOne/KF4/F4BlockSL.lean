module

public import CFSG.RankThree.PartOne.KF4.LongA2Frame
public import CFSG.RankThree.PartOne.KF4.ShortA2Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped MatrixGroups

section BlockSL

variable {L : Type} [Field L]

theorem blockSL_uSL (c : L) :
    blockSL L 2 1 (uSL c) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
  apply Subtype.ext
  rw [CFSG.LinearGroups.coe_transvection]
  have e0 : (finSumFinEquiv.symm (0 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inr 0 := rfl
  have h : ((blockSL L 2 1 (uSL c) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (uSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
  rw [h]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [reindex_apply, submatrix_apply, e0, e1, e2, coe_uSL, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]

theorem blockSL_vSL (c : L) :
    blockSL L 2 1 (vSL c) =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
  apply Subtype.ext
  rw [CFSG.LinearGroups.coe_transvection]
  have e0 : (finSumFinEquiv.symm (0 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 3) : Fin 2 ⊕ Fin 1) = Sum.inr 0 := rfl
  have h : ((blockSL L 2 1 (vSL c) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (vSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
  rw [h]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [reindex_apply, submatrix_apply, e0, e1, e2, coe_vSL, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]

end BlockSL

section Long

variable
  {L : Type} [Field L]

theorem f4rhoLong_blockSL (Y : SL(2, L)) :
    f4rhoLong L (blockSL L 2 1 Y) = simpleRootSL2 Tag.F4 L (f4Index 0) Y := by
  have hx : ∀ c : L, f4rhoLong L (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) c) = xUnit Tag.F4 L (f4Index 0) c := by
    intro c
    have hmem : xUnit Tag.F4 L (f4Index 0) c ∈ subsystemGroup Tag.F4 L f4LongSupport :=
      xUnit_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) c
    have hrep : f4LongRep L ⟨xUnit Tag.F4 L (f4Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
      apply Subtype.ext
      rw [coe_f4LongRep, CFSG.LinearGroups.coe_transvection]
      exact f4Long_Mat_x1 c
    rw [← hrep]
    exact f4rhoLong_f4LongRep hmem
  have hy : ∀ c : L, f4rhoLong L (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) c) = yUnit Tag.F4 L (f4Index 0) c := by
    intro c
    have hmem : yUnit Tag.F4 L (f4Index 0) c ∈ subsystemGroup Tag.F4 L f4LongSupport :=
      yUnit_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) c
    have hrep : f4LongRep L ⟨yUnit Tag.F4 L (f4Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
      apply Subtype.ext
      rw [coe_f4LongRep, CFSG.LinearGroups.coe_transvection]
      exact f4Long_Mat_y1 c
    rw [← hrep]
    exact f4rhoLong_f4LongRep hmem
  have key : (f4rhoLong L).comp (blockSL L 2 1) = simpleRootSL2 Tag.F4 L (f4Index 0) :=
    eq_simpleRootSL2 (f4Index 0) (fun c => by rw [MonoidHom.comp_apply, blockSL_uSL, hx])
      (fun c => by rw [MonoidHom.comp_apply, blockSL_vSL, hy])
  exact DFunLike.congr_fun key Y

end Long

section Short

variable
  {L : Type} [Field L]

theorem f4rhoShort_transvection_01 (c : L) :
    f4rhoShort L (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) =
      yUnit Tag.F4 L (f4Index 2) (-c) := by
  have hmem : yUnit Tag.F4 L (f4Index 2) (-c) ∈ subsystemGroup Tag.F4 L f4ShortSupport :=
    yUnit_mem_subsystemGroup ((mem_f4ShortSupport _).2 (Or.inl rfl)) _
  have hrep : f4ShortRep L ⟨yUnit Tag.F4 L (f4Index 2) (-c), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
    apply symRep_injective
    rw [← Mat_f4ShortRep]
    change f4Short_data.Mat (yUnit Tag.F4 L (f4Index 2) (-c)) = _
    have h := (Mat_pinnedX_simple_short (K := L)).2.1 (-c)
    rw [f4ShortSigma_values.2.2.1, pinnedX_neg_single, neg_neg] at h
    exact h
  rw [← hrep]
  exact f4rhoShort_f4ShortRep hmem

theorem f4rhoShort_transvection_10 (c : L) :
    f4rhoShort L (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) =
      xUnit Tag.F4 L (f4Index 2) (-c) := by
  have hmem : xUnit Tag.F4 L (f4Index 2) (-c) ∈ subsystemGroup Tag.F4 L f4ShortSupport :=
    xUnit_mem_subsystemGroup ((mem_f4ShortSupport _).2 (Or.inl rfl)) _
  have hrep : f4ShortRep L ⟨xUnit Tag.F4 L (f4Index 2) (-c), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
    apply symRep_injective
    rw [← Mat_f4ShortRep]
    change f4Short_data.Mat (xUnit Tag.F4 L (f4Index 2) (-c)) = _
    have h := (Mat_pinnedX_simple_short (K := L)).1 (-c)
    rw [f4ShortSigma_values.1, pinnedX_single, neg_neg] at h
    exact h
  rw [← hrep]
  exact f4rhoShort_f4ShortRep hmem

theorem WSL_mul_uSL_mul_inv (c : L) : (WSL : SL(2, L)) * uSL c * WSL⁻¹ = vSL (-c) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_WSL,
    coe_uSL, coe_vSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_mul_vSL_mul_inv (c : L) : (WSL : SL(2, L)) * vSL c * WSL⁻¹ = uSL (-c) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_WSL,
    coe_uSL, coe_vSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem f4rhoShort_blockSL (Y : SL(2, L)) :
    f4rhoShort L (blockSL L 2 1 Y) =
      simpleRootSL2 Tag.F4 L (f4Index 2) WSL * simpleRootSL2 Tag.F4 L (f4Index 2) Y *
        (simpleRootSL2 Tag.F4 L (f4Index 2) WSL)⁻¹ := by
  have key : (f4rhoShort L).comp (blockSL L 2 1) =
      (MulAut.conj (simpleRootSL2 Tag.F4 L (f4Index 2) WSL)).toMonoidHom.comp
        (simpleRootSL2 Tag.F4 L (f4Index 2)) := by
    refine MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change f4rhoShort L (blockSL L 2 1 (uSL c)) =
        simpleRootSL2 Tag.F4 L (f4Index 2) WSL * simpleRootSL2 Tag.F4 L (f4Index 2) (uSL c) *
          (simpleRootSL2 Tag.F4 L (f4Index 2) WSL)⁻¹
      rw [blockSL_uSL, f4rhoShort_transvection_01, ← map_inv, ← map_mul, ← map_mul,
        WSL_mul_uSL_mul_inv, simpleRootSL2_vSL]
    · change f4rhoShort L (blockSL L 2 1 (vSL c)) =
        simpleRootSL2 Tag.F4 L (f4Index 2) WSL * simpleRootSL2 Tag.F4 L (f4Index 2) (vSL c) *
          (simpleRootSL2 Tag.F4 L (f4Index 2) WSL)⁻¹
      rw [blockSL_vSL, f4rhoShort_transvection_10, ← map_inv, ← map_mul, ← map_mul,
        WSL_mul_vSL_mul_inv, simpleRootSL2_uSL]
  exact DFunLike.congr_fun key Y

end Short

end CFSG.RankThree.PartOne.KF4
