module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326S
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4Assembly
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoCentralizerZ
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixed
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812Outer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

theorem Counterexample4.false_of_not_quasisimpleModOTwo (c : Counterexample4 G)
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
    (hST : CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainNonAbelian) (hL3 : L3Overgroup) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, hp⟩ := c.sigma_nonempty
  have h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.conclusion76 c hp hSE
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 c.S.M
  obtain ⟨d, hdM, hdL, hdS, hinj, hcomp, hperm⟩ := c.toCtx812.exists_sylowThreeData h812 hP
  by_cases hI : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)
  · exact c.toCtx812.false_of_le_normalizer_Lf hp h76 d hdM hdL hP hdS hinj hperm hI
  obtain ⟨t, -, -⟩ :=
    c.toCtx812.exists_caseTwoTransitive outerThreeSplit_holds d hdM hdL hinj hcomp hperm hP hdS hI
  exact t.false_of_centralizer_Z_le hOut hSE
    (t.caseTwoResidual_of_inputs hK11 hK32 hGA hSp hK332 hOut hSch hNT hblk hKF1 hKF2 hK461 hK462
      hK49 (fun G _ _ hKP hsim hna K hK hM hFs R hnc _ =>
          hST G hKP hsim hna K hK hM hFs R hnc) hL3 hSE) hp h76 (t.centralizer_Z_le hK326 hp h76)

theorem theorem82Four_of_inputs (hK : KInputs811)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hS : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedSolvable)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hOut : PerfectAutInner)
    (hK326 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S) (hK11 : K11)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hNT : CFSG.AGLEmbedding.Asc81bNineThree) (hblk : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (hKF1 : L3NotEvenClassical) (hKF2 : L3EvenParabolic)
    (hK461 : CFSG.LocalAnalysis.UniquenessCase.UCK.K461)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hK49 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K49I)
    (hST : CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainNonAbelian) (hL3 : L3Overgroup) :
    CFSG.Yardstones.Mf4cdcdf2e013.Theorem82Four := by
  refine theorem82Four_of_isEmpty fun G _ _ c => ?_
  by_cases h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L
  · exact c.false_of_quasisimpleModOTwo h811 hK hSE (c.section8L4Residual hK hSE hS hK332)
  · exact c.false_of_not_quasisimpleModOTwo h811 hOut hSE hK326 hK11 hK32 hGA hSp hK332 hSch
      hNT hblk hKF1 hKF2 hK461 hK462 hK49 hST hL3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
