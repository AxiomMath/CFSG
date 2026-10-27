module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSecReal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFU4Fac
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem k146FFU4_holds :
    K146FFU4 := by
  intro W _ _ hW Y L n hO2 hL hU4 hn hA
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  have hLY : L ≤ Y := hL.1
  obtain ⟨hρ, hcomp', A', hA'cal, hA'L⟩ := ffSetup hL hA
  have hU4' : IsU4 ↥(L.subgroupOf Y) n :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hU4
  haveI : IsSimpleGroup ↥(L.subgroupOf Y) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4'
  obtain ⟨B, m, -, hBe, hBN, hm1, hm, hUinv, hXinv, hCB, hirr, hnt, hcost⟩ :=
    ffUnique_of_factorBound hρ hcomp' hA'cal hA'L (u4_factorBound hn hU4')
  obtain ⟨-, hnat⟩ :=
    u4_secNatural hn hU4' hBe hBN hm1 hm inf_le_left hUinv hXinv hCB hirr hnt hcost
  let e : ↥L ≃* ↥(secMulImg hUinv hXinv (L.subgroupOf Y)) :=
    (Subgroup.subgroupOfEquivOfLe hLY).symm.trans (secMulEquiv le_sup_left hUinv hXinv hnt)
  rcases hnat with hSU4 | hOm6
  · obtain ⟨⟨K₀, h₀, h₁, h₂, ⟨ψ⟩⟩, K, hK, hKf, hc, hreal⟩ :=
      Thm14_5.isSUn_natSUn_of_naturalSU4 hSU4
    exact Or.inl ⟨⟨K₀, h₀, h₁, h₂, ⟨e.trans ψ⟩⟩,
      K, hK, hKf, hc, ffSec_realizes hLY le_sup_left hUinv hXinv hnt hreal⟩
  · obtain ⟨⟨hev, K₀, h₀, h₁, b₀, c₀, h₂, h₃, ⟨ψ⟩⟩, hev', K, hK, hKf, b, c, hc, hq, hreal⟩ :=
      Thm14_5.isOmegaMinus_natOmegaMinus_of_naturalOmega6 hOm6
    exact Or.inr ⟨⟨hev, K₀, h₀, h₁, b₀, c₀, h₂, h₃, ⟨e.trans ψ⟩⟩,
      hev', K, hK, hKf, b, c, hc, hq, ffSec_realizes hLY le_sup_left hUinv hXinv hnt hreal⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
