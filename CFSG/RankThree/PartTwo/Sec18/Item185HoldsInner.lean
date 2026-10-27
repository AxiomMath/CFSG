module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerChev2
public import CFSG.RankThree.PartTwo.Sec18.Item185InnerJ3
public import CFSG.RankThree.PartTwo.Sec18.Item185NormIrredPerm
public import CFSG.RankThree.PartTwo.Sec18.Item185NormIrredLin
public import CFSG.RankThree.PartTwo.Sec18.Item185NormIrredBig

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp list42_of_rankHyp list42_alts)

section Assembly


theorem leafInner_holds : LeafInner := by
  refine leafInner_of_data ?_
  intro X _ _ hX A B c hd
  rcases list42_alts (list42_of_rankHyp hX) with h | h | h | h | h | h | h | h | h
  · exact innerCase_one normIrred_projSL_two_twentySeven X hX A B c hd h
  · exact innerCase_two X hX A B c hd h
  · exact innerCase_three X hX A B c hd h
  · exact innerCase_four X hX A B c hd h
  · exact innerCase_five normIrred_alternatingGroup_nine normIrred_alternatingGroup_ten
      normIrred_alternatingGroup_eleven X hX A B c hd h
  · exact innerCase_six noInnerData_J3 X hX A B c hd h
  · exact innerCase_seven normIrred_projSU_four_two normIrred_projSU_four_eight X hX A B c hd h
  · exact innerCase_eight normIrred_projSL_six_two normIrred_projSL_seven_two
      normIrred_projSp_three_two (fun b c hbc => normIrred_projOmegaMinus_three_two hbc)
      normIrred_projSL_four_four X hX A B c hd h
  · exact innerCase_nine X hX A B c hd h

end Assembly

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
