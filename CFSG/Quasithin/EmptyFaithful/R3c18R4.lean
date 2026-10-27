module

public import CFSG.Quasithin.EmptyFaithful.R3c18R3
public import CFSG.Quasithin.EmptyFaithful.R3c18T

public section

namespace CFSG.Quasithin

namespace R3c18

section Assembly

set_option linter.unusedSectionVars false


theorem qLiePRankRest3_of_shapes (hcls : D4Class) (hrk : D4Rank) : QLiePRankRest3 :=
  qLiePRankFam_d4 hcls hrk

theorem qLiePRank_of_shapes (hG2 : G2PRankShape) (hSp4 : Sp4PRankShape) (hL3 : L3PRankShape)
    (hU3 : U3PRankShape) (hF4cls : F4ReeClass) (hF4rk : F4ReeRank) (hD4cls : D4Class)
    (hD4rk : D4Rank) : QLiePRank :=
  qLiePRank_of_rest3 hG2 hSp4 hL3 hU3 hF4cls hF4rk (qLiePRankRest3_of_shapes hD4cls hD4rk)

end Assembly

end R3c18

end CFSG.Quasithin
