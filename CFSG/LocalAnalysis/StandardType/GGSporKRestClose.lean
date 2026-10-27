module

public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCo1Five
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCo1Seven
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCo1Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCo2Five
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCo2Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCo3Five
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCo3Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFi22
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFi22Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFi23Five
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFi23Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFi24Five
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFi24Seven
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFi24Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestHNFive
public import CFSG.LocalAnalysis.StandardType.GGSporKRestHNThree
public import CFSG.LocalAnalysis.StandardType.GGSporKRestHSFive
public import CFSG.LocalAnalysis.StandardType.GGSporKRestHSThree
public import CFSG.LocalAnalysis.StandardType.GGSporKRestHalf
public import CFSG.LocalAnalysis.StandardType.GGSporKRestHe
public import CFSG.LocalAnalysis.StandardType.GGSporKRestHeSeven
public import CFSG.LocalAnalysis.StandardType.GGSporKRestJ2Cover
public import CFSG.LocalAnalysis.StandardType.GGSporKRestJ3Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestJ4Eleven
public import CFSG.LocalAnalysis.StandardType.GGSporKRestJ4Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestLyFive
public import CFSG.LocalAnalysis.StandardType.GGSporKRestLyThree
public import CFSG.LocalAnalysis.StandardType.GGSporKRestM11Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestM12Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestM22Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestM23Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestM24Three
public import CFSG.LocalAnalysis.StandardType.GGSporKRestMcLFive
public import CFSG.LocalAnalysis.StandardType.GGSporKRestMcLThree
public import CFSG.LocalAnalysis.StandardType.GGSporKRestONan
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPairs
public import CFSG.LocalAnalysis.StandardType.GGSporKRestRuCover
public import CFSG.LocalAnalysis.StandardType.GGSporKRestSuzFive
public import CFSG.LocalAnalysis.StandardType.GGSporKRestSuzThree
public import CFSG.LocalAnalysis.StandardType.GGSporKRestThFive
public import CFSG.LocalAnalysis.StandardType.GGSporKRestThSeven
public import CFSG.LocalAnalysis.StandardType.GGSporKRestThThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRepBase
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate6104
public import Certificates.Certificate6105
public import Certificates.Certificate6106
public import Certificates.Certificate6108
public import Certificates.Certificate6109
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.StandardType.SporadicShape

theorem ggKGroupFusionAtFlatK_rest_closed :
    GGKGroupFusionAtFlatK GGKFSporadicRest :=
  ggKGroupFusionAtFlatK_rest_of_leaves
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicP2Table_holds
    (by
      rintro s p (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact sporKRest_cover_M12_3
      · exact sporKRest_cover_M22_3
      · exact sporKRest_cover_M23_3
      · exact sporKRest_cover_M24_3
      · exact sporKRest_cover_J2_3
      · exact sporKRest_cover_J2_5
      · exact sporKRest_cover_J4_3
      · exact sporKRest_cover_HS_3
      · exact sporKRest_cover_McL_3
      · exact sporKRest_cover_Suz_3
      · exact sporKRest_cover_Suz_5
      · exact sporKRest_cover_Ru_3
      · exact sporKRest_cover_Ru_5
      · exact sporKRest_cover_He_3
      · exact sporKRest_cover_He_5
      · exact sporKRest_cover_He_7
      · exact sporKRest_cover_Ly_3
      · exact sporKRest_cover_Ly_5
      · exact sporKRest_cover_ONan_3
      · exact sporKRest_cover_ONan_7
      · exact sporKRest_cover_Co1_3
      · exact sporKRest_cover_Co1_5
      · exact sporKRest_cover_Co1_7
      · exact sporKRest_cover_Co2_3
      · exact sporKRest_cover_Co2_5
      · exact sporKRest_cover_Co3_3
      · exact sporKRest_cover_Co3_5
      · exact sporKRest_cover_Fi22_3
      · exact sporKRest_cover_Fi23_3
      · exact sporKRest_cover_Fi23_5
      · exact sporKRest_cover_Fi24Prime_3
      · exact sporKRest_cover_Fi24Prime_5
      · exact sporKRest_cover_Fi24Prime_7
      · exact sporKRest_cover_HN_3
      · exact sporKRest_cover_HN_5
      · exact sporKRest_cover_Th_3
      · exact sporKRest_cover_Th_5
      · exact sporKRest_cover_Th_7)
    (by
      rintro s p (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact sporKRest_coverOrUnmarked_M11_3
      · exact sporKRest_coverOrUnmarked_HS_5
      · exact sporKRest_coverOrUnmarked_McL_5
      · exact sporKRest_coverOrUnmarked_J3_3
      · exact sporKRest_coverOrUnmarked_J4_11)
    sporKRest_fi22_exc_Fi22_5

end CFSG.StandardType.SporadicShape
