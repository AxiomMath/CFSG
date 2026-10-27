module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67OuterSO3Order
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutFixed
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddGroup
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Matrix MatrixGroups

theorem orderOf_le_of_outer_involution_psl_odd {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hp2 : p ≠ 2) (hq : p ^ f % 3 = 2) (hL : LieModel J .PSL 3 p f) {α : MulAut J}
    (hα : α ^ 2 = 1) (hαout : α ∉ (MulAut.conj : J →* MulAut J).range) {y : J} (hy : α y = y) :
    orderOf y ≤ p ^ f + 1 := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hp : p.Prime := hL.admissible.1
  have hodd : Odd f :=
    CFSG.RankThree.PartTwo.Sec20.L3OddGroup.odd_of_pow_mod_three_eq_two hq
  have hK2 : ringChar K ≠ 2 :=
    CFSG.GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hKcard
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  let β : MulAut (projectiveSL 3 K) := MulAut.congr e α
  have hβ2 : β * β = 1 := by
    have hα' : α * α = 1 := by simpa [pow_two] using hα
    change MulAut.congr e α * MulAut.congr e α = 1
    rw [← map_mul, hα', map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projectiveSL 3 K) := by
    intro h
    have h' : MulAut.congr e α ∈
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := h
    exact hαout
      (CFSG.RankThree.PartTwo.Sec20.L3OddGroup.mem_range_conj_of_congr e h')
  obtain ⟨A, hAsymm, hAeq⟩ :=
    CFSG.GH74.KGroups.L3Eps.lin_involution_form hp hKcard hodd h2 hβ2 hβout
  set x : projectiveSL 3 K := e y with hxdef
  have hx : β x = x := by
    have h1 : β x = e (α y) :=
      CFSG.RankThree.PartTwo.Sec20.L3OddGroup.congr_apply_apply e α y
    rw [h1, hy, hxdef]
  have hx' : (conjAut 3 K A * dualAut 3 K) x = x := by
    rw [← hAeq]; exact hx
  obtain ⟨z, hz⟩ := CFSG.QuasithinUnique.Ch1.exists_mem_soForm_of_fixed A hx'
  let R : GL (Fin 3) K := A⁻¹
  have hRsymm : (R : Matrix (Fin 3) (Fin 3) K)ᵀ = R :=
    CFSG.GH74.KGroups.L3Eps.transpose_inv_of_symm A hAsymm
  have hR0 : (R : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    intro h0
    have hmul : R * A = 1 := by
      change A⁻¹ * A = 1
      exact inv_mul_cancel A
    have h1 : (R : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, hmul, Units.val_one]
    rw [h0, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hInj : Function.Injective
      (CFSG.QuasithinUnique.Ch1.soProj (R : Matrix (Fin 3) (Fin 3) K)) :=
    CFSG.QuasithinUnique.Ch1.soProj_injective hR0
  let g : SL(3, K) := (z : SL(3, K))
  have hzg : (g : Matrix (Fin 3) (Fin 3) K)ᵀ * (R : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K) = (R : Matrix (Fin 3) (Fin 3) K) := z.2
  have hX : Matrix.SpecialLinearGroup.toGL g ∈
      CFSG.ComponentClassification.CatalogueBGraphForm.isometryGroup 3 K R := by
    rw [CFSG.ComponentClassification.CatalogueBGraphForm.mem_isometryGroup]
    change ((Matrix.SpecialLinearGroup.toGL g : Matrix (Fin 3) (Fin 3) K))ᵀ *
      (R : Matrix (Fin 3) (Fin 3) K) *
      (Matrix.SpecialLinearGroup.toGL g : Matrix (Fin 3) (Fin 3) K) =
      (R : Matrix (Fin 3) (Fin 3) K)
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hzg
  have hdet : ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact g.2
  have hbound : orderOf (Matrix.SpecialLinearGroup.toGL g) ≤ Nat.card K + 1 :=
    orderOf_le_card_add_one_of_isometry_three hK2 hRsymm hX hdet
  have horder_yz : orderOf y = orderOf z := by
    rw [← MulEquiv.orderOf_eq e y, ← hxdef, ← hz]
    exact orderOf_injective
      (CFSG.QuasithinUnique.Ch1.soProj (R : Matrix (Fin 3) (Fin 3) K)) hInj z
  have horder_zg : orderOf z = orderOf (Matrix.SpecialLinearGroup.toGL g) := by
    rw [← Subgroup.orderOf_coe z]
    exact (orderOf_injective (Matrix.SpecialLinearGroup.toGL)
      Matrix.SpecialLinearGroup.toGL_injective (z : SL(3, K))).symm
  calc orderOf y = orderOf z := horder_yz
    _ = orderOf (Matrix.SpecialLinearGroup.toGL g) := horder_zg
    _ ≤ Nat.card K + 1 := hbound
    _ = p ^ f + 1 := by rw [hKcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
