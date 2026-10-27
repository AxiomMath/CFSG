module

public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofInvD
public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSwapSylow
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProof
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Main1117

theorem item1117_of_res (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119) (h82 : Sec8.Item82One)
    (h1016 : Sec10.Item1016) (h1116 : Item1116) (hG2 : KFact1117CubeG2)
    (hL3 : KFact1117CubeL3) (hN : Gap1117NotActXNormal) (hS : Gap1117SwapSylow) : Item1117 :=
  item1117_of_steps h45 h48 h97 h113 h117 h118 h119 h82 h1016 h1116 hG2 hL3 hN hS
    (gap1117SwapOut_of h45 h97 h113 h117)

theorem item1117_of_res_W (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119) (h82 : Sec8.Item82One)
    (h1016 : Sec10.Item1016) (h1116 : Item1116) (hG2 : KFact1117CubeG2)
    (hL3 : KFact1117CubeL3) (hN : Gap1117NotActXNormal) (hSW : Gap1117SwapSylowW) :
    Item1117 :=
  item1117_of_res h45 h48 h97 h113 h117 h118 h119 h82 h1016 h1116 hG2 hL3 hN
    (gap1117SwapSylow_of_W h45 h113 h117 hSW)

end Main1117

section Main1118

theorem setUp1118_of_res5_invElt (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) (h11131 : Item11131) (h11133 : Item11133Field)
    (h1117 : Item1117) (hD4 : KFact1118Triality46) (hE : KFact1118InvElt) : SetUp1118 :=
  setUp1118_of_res5 h45 h46 h113 h117 h119 h11131 h11133 h1117 hD4
    (kFact1118Inverter_of_elt h45 h117 hE)

end Main1118

end CFSG.RankThree.PartTwo.Sec11
