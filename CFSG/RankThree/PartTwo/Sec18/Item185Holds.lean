module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterExc
public import CFSG.RankThree.PartTwo.Sec18.Item185OuterU38
public import CFSG.RankThree.PartTwo.Sec18.Item185OuterD42

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp list42_of_rankHyp list42_alts)

section Assembly



theorem leafOuter_of_gaps (hK1 : GapU48) (hK2 : GapL3Field) (hK3 : GapU3Field) (hK4 : GapReeF4) :
    LeafOuter := by
  refine leafOuter_of_data ?_
  intro X _ _ hX P A B c hd
  rcases list42_alts (list42_of_rankHyp hX) with h | h | h | h | h | h | h | h | h
  · exact outerCase_one X hX P A B c hd h
  · exact outerCase_two X hX P A B c hd h
  · exact outerCase_three X hX P A B c hd h
  · exact outerCase_four X hX P A B c hd h
  · exact outerCase_five X hX P A B c hd h
  · exact outerCase_six X hX P A B c hd h
  · exact outerCase_seven hK1 hK2 hK3 hK4 noOuterData_projSU_three_eight noOuterData_d42 X hX P A B c hd h
  · exact outerCase_eight X hX P A B c hd h
  · exact outerCase_nine X hX P A B c hd h

end Assembly

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
