module

public import CFSG.LocalAnalysis.EvenBN.GMSK.SporadicONOuter
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic (orderOf_proj_of_entry)

private def matSymSeven : Matrix (Fin 3) (Fin 3) PSL3Four.F4 := !![0, 1, 0; 1, 0, 1; 0, 1, 1]

private def sl3SymSeven : Matrix.SpecialLinearGroup (Fin 3) PSL3Four.F4 :=
  ⟨matSymSeven, by rw [Matrix.det_fin_three]; decide⟩

private theorem dualAut_proj_eq_inv_of_symmetric
    {g : Matrix.SpecialLinearGroup (Fin 3) PSL3Four.F4}
    (hg : (g : Matrix (Fin 3) (Fin 3) PSL3Four.F4).transpose = g) :
    LinearFlag.dualAut 3 PSL3Four.F4 (LinearFlag.proj 3 PSL3Four.F4 g) =
      (LinearFlag.proj 3 PSL3Four.F4 g)⁻¹ := by
  have hsym : (g⁻¹).transpose = g⁻¹ := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_transpose, hg]
  rw [LinearFlag.dualAut_proj, hsym, map_inv]

private theorem conj_inv {G : Type*} [Group G] {γ β φ : MulAut G} (hγ : γ = φ * β * φ⁻¹)
    {y : G} (hy : β y = y⁻¹) : γ (φ y) = (φ y)⁻¹ := by
  rw [hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hy,
    map_inv]

theorem exists_inv_seven_of_graph (A : GL (Fin 3) PSL3Four.F4)
    (hA : (LinearFlag.conjAut 3 PSL3Four.F4 A * LinearFlag.dualAut 3 PSL3Four.F4) ^ 2 = 1) :
    ∃ y : LinearFlag.projectiveSL 3 PSL3Four.F4,
      (LinearFlag.conjAut 3 PSL3Four.F4 A * LinearFlag.dualAut 3 PSL3Four.F4) y = y⁻¹ ∧
        orderOf y = 7 := by
  obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms (K := PSL3Four.F4) (f := 2)
      (by norm_num) CFSG.Sporadic.ONOddCore.card_F4 (le_refl 3) A hA
  have hC1 : C = 1 := by
    rcases hC with ⟨h, -⟩ | ⟨r, hr, -⟩
    · exact Units.ext h
    · omega
  rw [hC1, map_one, one_mul] at hHC
  have h7 : sl3SymSeven ^ 7 = 1 := Subtype.ext (by decide)
  have hinv : LinearFlag.dualAut 3 PSL3Four.F4
      (LinearFlag.proj 3 PSL3Four.F4 sl3SymSeven) =
      (LinearFlag.proj 3 PSL3Four.F4 sl3SymSeven)⁻¹ :=
    dualAut_proj_eq_inv_of_symmetric (by decide)
  refine ⟨LinearFlag.conjAut 3 PSL3Four.F4 H
      (LinearFlag.proj 3 PSL3Four.F4 sl3SymSeven), conj_inv hHC hinv, ?_⟩
  rw [MulEquiv.orderOf_eq]
  exact orderOf_proj_of_entry (by norm_num) h7 (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
