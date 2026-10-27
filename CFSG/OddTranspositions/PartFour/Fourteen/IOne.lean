module

public import CFSG.OddTranspositions.PartFour.Fourteen.Assembly
public import CFSG.OddTranspositions.Dichotomy
import CFSG.OddTranspositions.PartFour.Fourteen.TableHolds
import CFSG.OddTranspositions.TheoremTwo.TheoremTwo
public import CFSG.Timmesfeld.Bridge.Asc72ZMain

public section

namespace CFSG.OddTranspositions.PartFour

theorem noSqE1OrThreeTranspositions_of_inputs
    (h88 : PartThree.Theorem8_8Quot) (h4 : Theorem4List) (h5 : Theorem5List) :
    NoSqE1OrThreeTranspositions :=
  noSqE1OrThreeTranspositions_of_main
    (ascMainTheorem_of_inputs CFSG.Timmesfeld.Bridge.Asc72.theoremOne aschbacherTheoremTwo_holds
      h88 h4 h5) ascListTable_holds

theorem oddTranspNoSqE1Dich_of_inputs
    (h88 : PartThree.Theorem8_8Quot) (h4 : Theorem4List) (h5 : Theorem5List) :
    CFSG.RankThree.GF2n.Tim79a.OddTranspNoSqE1Dich :=
  oddTranspNoSqE1Dich_of_classification
    (ascNoSqDichotomy (noSqE1OrThreeTranspositions_of_inputs h88 h4 h5))

end CFSG.OddTranspositions.PartFour
