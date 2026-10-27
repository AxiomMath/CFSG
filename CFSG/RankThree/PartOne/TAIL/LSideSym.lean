module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.RankThree.PartOne.TAIL.LSideModel

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix Subgroup
open CFSG.RankThree.PartOne.MB3 (D2 bd2 coe_D2 slRe coe_slRe)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)

theorem slGraphAut_eq_inv_of_symm {n : ℕ} {F : Type} [Field F]
    (g : SpecialLinearGroup (Fin n) F) (h : (g : Matrix (Fin n) (Fin n) F).transpose = g) :
    slGraphAut n F g = g⁻¹ := by
  apply Subtype.ext
  rw [slGraphAut_matrix]
  show ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).transpose =
    ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose, h]

section Sym

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem b1_comm_b2 : (b1 : SLX κ) * b2 = b2 * b1 := by
  rw [b1, b2, ← map_mul, ← map_mul]
  congr 1
  simp

theorem slRe_b1_symm {Y : Type} [Fintype Y] [DecidableEq Y] (e0 : (Fin 3 ⊕ Fin 3) ⊕ κ ≃ Y) :
    ((slRe e0 (b1 : SLX κ) : SpecialLinearGroup Y (ZMod 2)) : Matrix Y Y (ZMod 2)).transpose =
      slRe e0 (b1 : SLX κ) := by
  rw [coe_slRe, Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex]
  congr 1
  simp [b1, coe_D2, bd2, Matrix.fromBlocks_transpose, sM_transpose, coe_sSL]

theorem slRe_b2_symm {Y : Type} [Fintype Y] [DecidableEq Y] (e0 : (Fin 3 ⊕ Fin 3) ⊕ κ ≃ Y) :
    ((slRe e0 (b2 : SLX κ) : SpecialLinearGroup Y (ZMod 2)) : Matrix Y Y (ZMod 2)).transpose =
      slRe e0 (b2 : SLX κ) := by
  rw [coe_slRe, Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex]
  congr 1
  simp [b2, coe_D2, bd2, Matrix.fromBlocks_transpose, sM_transpose, coe_sSL]

theorem graph_slRe_eB {n : ℕ} (e0 : (Fin 3 ⊕ Fin 3) ⊕ κ ≃ Fin n) (i j : ℤ) :
    slGraphAut n (ZMod 2) (slRe e0 (eB κ i j)) = (slRe e0 (eB κ i j))⁻¹ := by
  have h1 : slGraphAut n (ZMod 2) (slRe e0 (b1 : SLX κ)) = (slRe e0 (b1 : SLX κ))⁻¹ :=
    slGraphAut_eq_inv_of_symm _ (slRe_b1_symm e0)
  have h2 : slGraphAut n (ZMod 2) (slRe e0 (b2 : SLX κ)) = (slRe e0 (b2 : SLX κ))⁻¹ :=
    slGraphAut_eq_inv_of_symm _ (slRe_b2_symm e0)
  have hc : slRe e0 (b1 : SLX κ) * slRe e0 (b2 : SLX κ) =
      slRe e0 (b2 : SLX κ) * slRe e0 (b1 : SLX κ) := by
    rw [← map_mul, ← map_mul, b1_comm_b2]
  have hz : slRe e0 (eB κ i j) = slRe e0 (b1 : SLX κ) ^ i * slRe e0 (b2 : SLX κ) ^ j := by
    rw [eB, map_mul, map_zpow, map_zpow]
  rw [hz, map_mul, map_zpow, map_zpow, h1, h2, _root_.mul_inv_rev, _root_.inv_zpow, _root_.inv_zpow]
  exact ((Commute.zpow_zpow hc i j).inv_inv).eq

end Sym

end CFSG.RankThree.PartOne.TAIL
