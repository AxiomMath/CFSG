module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSecReal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSp4Fac
public import CFSG.Quasithin.Background.SmithB42Sp4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem ffChiefSp4_section {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hL : IsComponentOf L Y) (hn : 1 < n) (hSp : IsSp4 ↥L n) (hA : ∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) :
    IsIrrOn L (commV L) (commV L ⊓ fixV L) ∧
      BinaryNaturalSp4 L (commV L) (commV L ⊓ fixV L) n := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  have hLY : L ≤ Y := hL.1
  obtain ⟨hρ, hcomp', A', hA'cal, hA'L⟩ := ffSetup hL hA
  have hSp' : IsSp4 ↥(L.subgroupOf Y) n :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hSp
  haveI : IsSimpleGroup ↥(L.subgroupOf Y) := UC22.K148.isSimpleGroup_of_isSp4 hSp'
  obtain ⟨hn2, K, _, _, _, hK, ⟨e⟩⟩ := UC22.K148.exists_antiSp_of_isSp4 hSp'
  obtain ⟨B, m, -, hBe, hBN, hm1, hm, hUinv, hXinv, hCB, hirr, hnt, hcost⟩ :=
    ffUnique_of_factorBound hρ hcomp' hA'cal hA'L (sp4_factorBound hn2 hK e)
  have hirrL := sp4_lemmaR hn2 hK e hBe hBN hm1 hm inf_le_left hUinv hXinv hCB hirr hnt hcost
  obtain ⟨i, φ, hφ⟩ :=
    sp4_secCoords hn2 hK e hBe hBN hm1 hm inf_le_left hUinv hXinv hCB hirrL hnt hcost
  have hbin : BinaryNaturalSp4 (secMulImg hUinv hXinv (L.subgroupOf Y)) ⊤ ⊥ n := by
    refine CFSG.Quasithin.B42Sp4.binaryNaturalSp4_of_coords (MulEquiv.refl _) hK
      ((secMulEquiv le_sup_left hUinv hXinv hnt).symm.trans e) i φ (fun g w => ?_)
    have h1 := hφ (e.symm g) w
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, secMulEquiv_apply, binPsi_secMul]
  obtain ⟨K', hK', hKf', hc', hreal⟩ := hbin
  exact ⟨ffSec_isIrrOn hLY hirrL hnt,
    K', hK', hKf', hc', ffSec_realizes hLY le_sup_left hUinv hXinv hnt hreal⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
