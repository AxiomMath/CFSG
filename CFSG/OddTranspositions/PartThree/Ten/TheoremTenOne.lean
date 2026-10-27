module

public import CFSG.OddTranspositions.PartThree.Ten.Assembly
import CFSG.OddTranspositions.PartThree.Ten.TenTwoQ
import CFSG.OddTranspositions.PartThree.Ten.TenThree
import CFSG.OddTranspositions.PartThree.Ten.TenFour

public section

namespace CFSG.OddTranspositions.PartThree

theorem theorem10_1_of_theorem8_7
    (h87 : Theorem8_7) : Theorem10_1 :=
  theorem10_1_of_tenFour (tenFour_of_tenThree (tenThree_of_tenTwo tenTwo_holds) h87)

end CFSG.OddTranspositions.PartThree

end
