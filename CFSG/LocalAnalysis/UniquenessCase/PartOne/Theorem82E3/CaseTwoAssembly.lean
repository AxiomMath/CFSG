module


public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Carrier
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCExcluded3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326S
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoCentralizerZ
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixed
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812Outer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K11 L3Overgroup L3EvenParabolic L3NotEvenClassical PerfectAutInner outerThreeSplit_holds)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem Ctx82E3.false_of_not_quasisimpleModOTwo (c : Ctx82E3 D) (X : Ctx82E3.C4Data G D.M)
    (hSC : c.SCExcluded3)
    (h812 : ¬ CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hOut : PerfectAutInner)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S) (hK11 : K11)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hNT : CFSG.AGLEmbedding.Asc81bNineThree) (hblk : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (hKF1 : L3NotEvenClassical) (hKF2 : L3EvenParabolic)
    (hK461 : CFSG.LocalAnalysis.UniquenessCase.UCK.K461)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hK49 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K49I)
    (hST : CFSG.CGT.PushingUpLit.SolKNA.SolomonTimmesfeldMainRankGe2) (hL3 : L3Overgroup) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, hp⟩ := c.sig_nonempty
  have hdvd : p ∣ ((c.L).subgroupOf D.M).index := by
    by_contra hnd
    exact hSC p ⟨hp, hnd⟩
  have hp' : p ∈ (c.toCtx812 X).sig := ⟨hp, hdvd⟩
  have h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p :=
    c.conclusion76 hp
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨d, hdM, hdL, hdS, hinj, hcomp, hperm⟩ := (c.toCtx812 X).exists_sylowThreeData h812 hP
  by_cases hI : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)
  · exact (c.toCtx812 X).false_of_le_normalizer_Lf hp' h76 d hdM hdL hP hdS hinj hperm hI
  obtain ⟨t, -, -⟩ :=
    (c.toCtx812 X).exists_caseTwoTransitive outerThreeSplit_holds d hdM hdL hinj hcomp hperm hP
      hdS hI
  exact t.false_of_centralizer_Z_le hOut hSE
    (t.caseTwoResidual_of_inputs hK11 hK32 hGA hSp hK332 hOut hSch hNT hblk hKF1 hKF2 hK461 hK462
      hK49 hST hL3 hSE) hp' h76 (t.centralizer_Z_le hK326 hp' h76)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
