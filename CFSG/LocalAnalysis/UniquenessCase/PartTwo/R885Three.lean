module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneEightThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R856Three
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKPorts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xK85
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves2Proofs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKList880SylowGen
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKList880NotSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]


theorem r885_dataOfSetup
    (hGF : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause)
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (hMS : S.InMSigma) : PartOne.Section8.R885 (dataOfSetup hS S) := by
  have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 : PartOne.Section7.StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have h63 := r6_3_dataOfSetup hS hUC hC S
  have h76 : UC22.F07.R76Sig (dataOfSetup hS S) := r76Sig_dataOfSetup hSE5 hSE3 hS S
  have h856 : PartOne.Section8.R856 (dataOfSetup hS S) :=
    PartOne.Section8.r856_dataOfSetup hS hUC hC S hMS
  have hSL3 := PartOne.Section8.list880NotSL3PiType
  have h881 : PartOne.Section8.R881 (dataOfSetup hS S) :=
    PartOne.Section8.r881_of_r82 _ (r82_dataOfSetup hGF hS hUC hC S hMS)
  have h882 : PartOne.Section8.R882 (dataOfSetup hS S) := PartOne.Section8.r882_of_r881 _ hSg h881
  have h883 : PartOne.Section8.R883 (dataOfSetup hS S) :=
    PartOne.Section8.r883_of_inputs _ hSg h76 h856 h881 h882 hSL3
      PartOne.Section8.list880SylowThreeTwoGenerated
  exact PartOne.Section8.r885_of_inputs _ hSg (UC22.dataExt_ofSetup hS S) h63 h76 h856 h881 h882
    h883 hSL3 PartOne.Section8.list880PRankInspection_holds PartOne.Section8.j2FivePRank_holds
    PartOne.Section8.list880CentralizerRanks_holds PartOne.Section8.list880ThreeInE9_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
