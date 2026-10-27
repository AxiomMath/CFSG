module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106KComp
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

theorem r8106_at_holds {G : Type} [Group G] [Finite G] {D : Data G} (hSg : SigmaStd D)
    (h61 : UC6.R6_1 D) {L P : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (h8103 : R8103At D L P p n) : R8106At D L P n :=
  r8106_at_of_kFacts kU45Lines_holds kU45Syl3_holds UCK.k462_holds
    (CFSG.LocalAnalysis.RankThreeUC.S15.kSch_of_catalog
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds)
    (kU3Ident_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds UCK.k32_holds)
    kU3Mult_holds kU3Facts_holds hSg hH h8103 (R8105.r8_105_at_holds hSg h61 hH h8103)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
