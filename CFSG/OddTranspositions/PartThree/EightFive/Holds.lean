module

public import CFSG.OddTranspositions.PartThree.EightFive.Assembly
public import CFSG.OddTranspositions.PartThree.EightFive.CaseTwo

public section

namespace CFSG.OddTranspositions.PartThree


theorem theorem8_5_holds : Theorem8_5 :=
  theorem8_5_of_caseTwo eightFiveCaseTwo_holds

theorem theorem8_7_holds : Theorem8_7 :=
  theorem8_7_of_caseTwo eightFiveCaseTwo_holds

end CFSG.OddTranspositions.PartThree
