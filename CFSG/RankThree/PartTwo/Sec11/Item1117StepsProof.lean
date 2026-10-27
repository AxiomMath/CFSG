module

public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofNotAct
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofSwap

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Main


theorem item1117_of_steps (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119) (h82 : Sec8.Item82One)
    (h1016 : Sec10.Item1016) (h1116 : Item1116) (hG2 : KFact1117CubeG2)
    (hL3 : KFact1117CubeL3) (hN : Gap1117NotActXNormal) (hS : Gap1117SwapSylow)
    (hO : Gap1117SwapOut) : Item1117 :=
  have hND := kFact1117Cube_of h45 h117 h118 hG2 hL3
  item1117_of_swap h45 h48 h97 h113 h117 h118 h119 h82 h1016
    (gap1117NotActX_of h45 h113 h117 h118 h119 h82 hND hN)
    (gap1117SymmetrySwap_of_exchange h45 h97 h113 h117 h119 h1116 hND hS hO) hND

end Main

end CFSG.RankThree.PartTwo.Sec11
