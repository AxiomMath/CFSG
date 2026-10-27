module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommEmbeddedDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardRoot

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixEmb_e1_aux_elt (i : Axis) :
    FullCenterWeyl.weylElt K i.swap * FullCenterWeyl.weylElt K i * FullCenterWeyl.weylElt K i.swap =
      RootStandard.rootSLHom K i FullCenterWeyl.swapSL := by
  apply antiSp_ext
  change glMat (FullCenterWeyl.weylElt K i.swap : Matrix.GeneralLinearGroup (Fin 4) K) *
      glMat (FullCenterWeyl.weylElt K i : Matrix.GeneralLinearGroup (Fin 4) K) *
      glMat (FullCenterWeyl.weylElt K i.swap : Matrix.GeneralLinearGroup (Fin 4) K) =
    glMat (RootStandard.rootSLHom K i FullCenterWeyl.swapSL :
      Matrix.GeneralLinearGroup (Fin 4) K)
  simp only [FullCenterWeyl.glMat_weylElt, RootStandard.glMat_rootSLHom,
    FullCenterWeyl.coe_swapSL]
  cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Axis.swap, FullCenterWeyl.weylMat, RootStandard.rootMat, Matrix.mul_apply,
      Fin.sum_univ_four]

theorem sixEmb_e1_aux_coe (φ : L ≃* antiSp K) (i : Axis) :
    RootStandard.rootHom φ i FullCenterWeyl.swapSL = embTau φ i := by
  have hel := sixEmb_e1_aux_elt (K := K) i
  change ((φ.symm (RootStandard.rootSLHom K i FullCenterWeyl.swapSL) : L) : G) =
    ((φ.symm (FullCenterWeyl.weylElt K i.swap) : L) : G) *
      ((φ.symm (FullCenterWeyl.weylElt K i) : L) : G) *
      ((φ.symm (FullCenterWeyl.weylElt K i.swap) : L) : G)
  rw [← hel]
  simp only [map_mul, Subgroup.coe_mul]

theorem sixEmb_e1_of_four_le (hK : 4 ≤ Nat.card K) (φ : L ≃* antiSp K) (i : Axis) :
    EmbE1Concl φ i := by
  show embTau φ i ∈ Sk φ i
  rw [show Sk φ i = (RootStandard.rootHom φ i).range from RootStandard.S_eq φ hK i,
    MonoidHom.mem_range]
  exact ⟨FullCenterWeyl.swapSL, sixEmb_e1_aux_coe φ i⟩

theorem sixEmb_e1_aux_four_le (hS : SCSetting L K n φ t i) : 4 ≤ Nat.card K := by
  rw [hS.fc.setup.card_K]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.fc.setup.two_le

theorem sixEmb_e1 (hS : SCSetting L K n φ t i) : EmbE1Concl φ i :=
  sixEmb_e1_of_four_le (sixEmb_e1_aux_four_le hS) φ i

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
