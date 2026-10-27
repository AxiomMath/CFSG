module

public import CFSG.Quasithin.EmptyFaithful.S146G5
public import CFSG.Quasithin.EmptyFaithful.S146B1
public import CFSG.Quasithin.EmptyFaithful.S146B3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stageSection146_of_inputs_five (h1413 : StageLemma1413) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hedge : GoldschmidtEdgeBoundSubgroups.{0})
    (h2 : Stage1461Two) (h3 : Stage1461Three) (h5 : Stage1461Five)
    (h12 : Stage14612) (h15 : Stage14615) (h17 : Stage14617) (hrank : Stage14611Rank)
    (h20 : Stage14620) (h21 : Stage14621) (h22 : Stage14622)
    (h23 : Stage14623) (hD4 : Stage146D4) (h24 : Stage14624)
    (hF1 : Stage146FRank) (hF2 : Stage146FH2) (hF3 : Stage146FFour)
    (h9 : Stage1469) (h105 : Stage14610Five) (h634 : Stage1463Four) : StageSection146 :=
  stageSection146_of_inputs_three h1413 h11 h113 hedge h2 h3 h5 h12 h15 h17 hrank
      (stage146BranchBCore_of_parts stage14619_proof h20 h21 h22 h23 hD4 h24 hF1 hF2 hF3) h9 h105
      h634

end CFSG.Quasithin
