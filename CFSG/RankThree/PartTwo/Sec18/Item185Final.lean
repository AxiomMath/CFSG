module

public import CFSG.RankThree.PartTwo.Sec18.Item185Holds
public import CFSG.RankThree.PartTwo.Sec18.Item185GapU48
public import CFSG.RankThree.PartTwo.Sec18.Item185GapL3
public import CFSG.RankThree.PartTwo.Sec18.Item185GapU3
public import CFSG.RankThree.PartTwo.Sec18.Item185GapReeF4

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

section ReeF4


theorem gapReeF4_holds : GapReeF4 := gapReeF4_fixedFacts

end ReeF4

section Assembly


theorem leafOuter_holds : LeafOuter :=
  leafOuter_of_gaps gapU48_holds gapL3Field_holds gapU3Field_holds gapReeF4_holds

end Assembly

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
