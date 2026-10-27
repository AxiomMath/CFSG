module

public import CFSG.Quasithin.EmptyFaithful.S146G3
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stage146BranchACore_of_parts_two (h2 : Stage1461Two) (h3 : Stage1461Three)
    (h12 : Stage14612) (h15 : Stage14615) (h17 : Stage14617) (hrank : Stage14611Rank) :
    Stage146BranchACore :=
  stage146BranchACore_of_parts (stage1461Four_of h2 h3) h12 h15 h17 hrank (stage14611H2_of h2)

theorem stageSection146_of_inputs_three (h1413 : StageLemma1413) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hedge : GoldschmidtEdgeBoundSubgroups.{0})
    (h2 : Stage1461Two) (h3 : Stage1461Three) (h5 : Stage1461Five)
    (h12 : Stage14612) (h15 : Stage14615) (h17 : Stage14617) (hrank : Stage14611Rank)
    (hB : Stage146BranchBCore) (h9 : Stage1469) (h105 : Stage14610Five)
    (h634 : Stage1463Four) : StageSection146 :=
  stageSection146_of_inputs h11 h113 hedge
      (stage146BranchACore_of_parts_two h2 h3 h12 h15 h17 hrank) hB h9 h105 stage1463_one_proof
      (stage1463_two_of (stage1461Six_of h2 h3 h5)) (stage1463_three_proof h1413) h634

end CFSG.Quasithin
