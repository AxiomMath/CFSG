module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSecReal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFG2Fac
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem ffChiefG2_section
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} {n : ℕ}
    (hL : IsComponentOf L Y) (hn : 1 < n) (hodd : Odd n) (hG2 : IsG2 ↥L n)
    (hA : ∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) :
    IsIrrOn L (commV L) (commV L ⊓ fixV L) ∧ G2Natural L (commV L) (commV L ⊓ fixV L) n := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  have hLY : L ≤ Y := hL.1
  obtain ⟨hρ, hcomp', A', hA'cal, hA'L⟩ := ffSetup hL hA
  have hG2' : IsG2 ↥(L.subgroupOf Y) n :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hG2
  haveI : IsSimpleGroup ↥(L.subgroupOf Y) :=
    CFSG.LocalAnalysis.EvenBN.G2.isSimpleGroup_of_lieModel_G2 hG2'
  have hCE := ((LieModel.chevalleyExceptional_iff (t := .G2) (p := 2) (f := n)
    (by decide)).1 hG2').2
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel hCE
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨B, m, -, hBe, hBN, hm1, hm, hUinv, hXinv, hCB, hirr, hnt, hcost⟩ :=
    ffUnique_of_factorBound hρ hcomp' hA'cal hA'L (g2_factorBound hodd hn hG2')
  have hirrL := (g2_innerOnSec hodd hn hG2' hBe hBN inf_le_left hUinv hXinv hirr).2
  obtain ⟨-, -, φ, hφ⟩ :=
    g2_secNatural hodd hn hG2' hK e hBe hBN hm1 hm inf_le_left hUinv hXinv hCB hirr hnt hcost
  have hg2 : G2Natural (secMulImg hUinv hXinv (L.subgroupOf Y)) ⊤ ⊥ n := by
    refine CFSG.Quasithin.B42G2F.g2Natural_of_coords hK
      ((secMulEquiv le_sup_left hUinv hXinv hnt).symm.trans e)
      (fun w => φ (Multiplicative.toAdd w)) (fun u v => map_add φ _ _)
      (fun u v h => φ.injective h) (fun y => ⟨Multiplicative.ofAdd (φ.symm y), by simp⟩)
      (fun l w => ?_)
    obtain ⟨l₀, rfl⟩ := (secMulEquiv le_sup_left hUinv hXinv hnt).surjective l
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, secMulEquiv_apply, secMul_apply]
    exact hφ l₀ (Multiplicative.toAdd w)
  obtain ⟨K', hK', hKf', hc', hreal⟩ := hg2
  exact ⟨ffSec_isIrrOn hLY hirrL hnt,
    K', hK', hKf', hc', ffSec_realizes hLY le_sup_left hUinv hXinv hnt hreal⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
