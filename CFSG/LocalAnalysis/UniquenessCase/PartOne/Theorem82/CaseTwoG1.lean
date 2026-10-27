module

public import CFSG.CGT.PushingUpLit.SolKNA.Residue

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoResidualSplit
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs49
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoVStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFaithful
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyModule
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKySL2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoC4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem caseTwoG1_of_uniqueTwoLocalKy (X : C4Data G c.S.M)
    (hK461 : CFSG.LocalAnalysis.UniquenessCase.UCK.K461)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hK49 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K49I)
    (hST : CFSG.CGT.PushingUpLit.SolKNA.SolomonTimmesfeldMainRankGe2)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    (hP1 : t.UniqueTwoLocalKy) : t.CaseTwoG1 := by
  intro p hp h76 hN _ hZ _
  by_contra hO
  obtain ⟨r, U, W, hr, -, hUW, hUO, hWM, hUMW, hfix⟩ :=
    t.exists_vStar hK32 hGA hSp hSch hZ hO
  have hfaith : ∀ k ∈ t.Ky, (∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ W) → k = 1 := fun k hk hkU =>
    t.eq_one_of_centralizes_section hK32 hGA hSp hP1 hUW hUO hWM hUMW hfix hk hkU
  rcases t.Ky_cases hK461 hK462 hK32 hGA hSp hK332 hOut hp hN hZ hr hUW hfix hfaith with
    h | h | h
  · exact t.not_nonempty_mulEquiv_SL2 h
  · exact t.not_lieModel_PSL2 h
  · exact t.not_isExt_Ky X hK49 hST hK32 hGA hSp hN h

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
