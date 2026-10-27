module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBLemmas
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLRound
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Round12


theorem ggBstarInnerDiagLInputOn_true_of_openLIDRound12
    (hLIDr : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRound12Label) :
    GGBstarInnerDiagLInputOn fun _ _ => True :=
  ggBstarInnerDiagLInputOn_true_of_cover
    (S := fun p lab => GGTypeALabel p lab ∨ GGCorFourTwoRestLabel p lab)
    (fun p lab _ _ => em (GGTypeALabel p lab))
    (ggBstarInnerDiagLInputOn_typeA.or
      (ggBstarInnerDiagLInputOn_rest_of_restSp
        (ggBstarInnerDiagLInputOn_restSp_of_restLID
          (ggBstarInnerDiagLInputOn_restLID_of_open
            (ggBstarInnerDiagLInputOn_openLID_of_rest ggLNoncyclicInput_holds
              (ggBstarInnerDiagLInputOn_openLIDRest_of_rest3
                TwF4SUThree.ggTwF4ThreeRankInput_holds
                (ggBstarInnerDiagLInputOn_rest3_of_round12 hLIDr)))))))

end Round12

end CFSG.StandardType
