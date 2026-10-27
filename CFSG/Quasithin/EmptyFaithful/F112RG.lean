module

public import CFSG.Quasithin.EmptyFaithful.F112F53Res
public import CFSG.Quasithin.EmptyFaithful.F112RE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input15208F112Rest_of_models (hGoldP : F6.GoldschmidtCharTwoLargePair.{0})
    (hHay : HayashiFiveThree) (hTits : TitsRankLeFive) (hF4 : TwistedF4RankLeFive)
    (hR : Input15208F53Res) (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207) (h15201 : StageLemma15201) (h15112 : StageLemma15112) :
    Input15208F112Rest :=
  ⟨input15208F112At_S3_S3_of_gold hGoldP h1515 h1519 h15207 h15201 h15112,
    (input15208F112At_S3_five_of_hay hHay hTits hF4 h1515 h1519 h15207 h15201 h15112).1,
    (input15208F112At_S3_five_of_hay hHay hTits hF4 h1515 h1519 h15207 h15201 h15112).2,
    input15208F112At_S5_S3_of_res hR h1515 h1519 h15207 h15201 h15112⟩

end CFSG.Quasithin
