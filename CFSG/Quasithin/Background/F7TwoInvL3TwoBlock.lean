module

public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.CGT.Timmesfeld75.L2Aut

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.CGT.Timmesfeld75
open CFSG.LieType.Steinberg.SL (blockHom blockMat blockEquiv blockMat_apply blockEquiv_inr
  ext_blockEquiv blockHom_injective blockMat_transvection_upper blockMat_transvection_lower)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def sl3BlockRho (K : Type) [Field K] (i : Fin 2) :
    SL(2, K) →* projectiveSL 3 K :=
  (proj 3 K).comp (blockHom K i)

theorem sl3BlockRho_apply (i : Fin 2) (g : SL(2, K)) :
    sl3BlockRho K i g = proj 3 K (blockHom K i g) := rfl

theorem coe_blockHom_matrix (i : Fin 2) (g : SL(2, K)) :
    ((blockHom K i g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat i (g : Matrix (Fin 2) (Fin 2) K) := rfl

theorem sl3BlockRho_injective (i : Fin 2) : Function.Injective (sl3BlockRho K i) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.mp hg
  obtain ⟨a, ha1, ha2⟩ := Fin.exists_ne_and_ne_of_two_lt i.castSucc i.succ (by omega)
  have hna : ¬(a = i.castSucc ∨ a = i.succ) := fun h => h.elim ha1 ha2
  have h1 := blockMat_apply i (g : Matrix (Fin 2) (Fin 2) K) (Sum.inr ⟨a, hna⟩) (Sum.inr ⟨a, hna⟩)
  rw [blockEquiv_inr] at h1
  have h2 : (blockHom K i g : Matrix (Fin 3) (Fin 3) K) a a = 1 := by
    rw [coe_blockHom_matrix, h1]
    simp
  have hc1 : (c : K) = 1 := by
    rw [hc] at h2
    simpa using h2
  refine blockHom_injective i (Subtype.ext ?_)
  rw [hc, hc1]
  simp

theorem blockMat_map_ringHom (i : Fin 2) (σ : K →+* K) (A : Matrix (Fin 2) (Fin 2) K) :
    (blockMat i A).map σ = blockMat i (A.map σ) := by
  refine ext_blockEquiv i fun p q => ?_
  rw [Matrix.map_apply, blockMat_apply, blockMat_apply]
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, apply_ite σ]

theorem blockMat_transpose_two (i : Fin 2) (A : Matrix (Fin 2) (Fin 2) K) :
    (blockMat i A)ᵀ = blockMat i Aᵀ := by
  refine ext_blockEquiv i fun p q => ?_
  rw [Matrix.transpose_apply, blockMat_apply, blockMat_apply]
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, eq_comm]

theorem fieldAut_sl3BlockRho (i : Fin 2) (σ : K ≃+* K) (g : SL(2, K)) :
    fieldAut 3 K σ (sl3BlockRho K i g) = sl3BlockRho K i (sl2FieldAut σ g) := by
  rw [sl3BlockRho_apply, sl3BlockRho_apply, fieldAut_proj]
  congr 1
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.map_apply_coe, coe_blockHom_matrix, coe_blockHom_matrix,
    RingHom.mapMatrix_apply, blockMat_map_ringHom]
  rfl

theorem dualAut_sl3BlockRho (i : Fin 2) (g : SL(2, K)) :
    dualAut 3 K (sl3BlockRho K i g) = sl3BlockRho K i (slGraphAut 2 K g) := by
  rw [sl3BlockRho_apply, sl3BlockRho_apply, dualAut_proj]
  congr 1
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.coe_transpose, ← map_inv, coe_blockHom_matrix, coe_blockHom_matrix]
  rw [slGraphAut_matrix, blockMat_transpose_two]

end CFSG.Quasithin.F7Two
