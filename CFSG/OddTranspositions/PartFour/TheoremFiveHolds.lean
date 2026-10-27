module

public import CFSG.OddTranspositions.PartFour.TheoremFiveMeetsSq
public import CFSG.OddTranspositions.PartThree.EightFive.Holds
public import CFSG.OddTranspositions.PartFour.Fourteen.TheoremFive
import CFSG.OddTranspositions.PartThree.EightNine.Main
import CFSG.OddTranspositions.PartFour.TheoremFiveList

public section

namespace CFSG.OddTranspositions.PartFour


theorem theorem5_of_theorem11_3 (h113 : PartThree.Theorem11_3) : Theorem5 :=
  theorem5_of_partThree PartThree.theorem8_7_holds
    (PartThree.lemma8_9_of_theorem8_7 PartThree.theorem8_7_holds) h113

theorem theorem5List_of_theorem11_3 (h113 : PartThree.Theorem11_3) : Theorem5List :=
  theorem5List_of_theorem5 (theorem5_of_theorem11_3 h113)

end CFSG.OddTranspositions.PartFour
