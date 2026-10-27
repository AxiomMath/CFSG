module

public import CFSG.RankThree.PartTwo.Sec11.LStarL3
public import CFSG.RankThree.PartTwo.KFacts.K72L3Field

public section

namespace CFSG.RankThree.PartTwo.Sec11

theorem lThreeMinusPiNoFixedSylow : LThreeMinusPiNoFixedSylow :=
  fun _ _ _ _ hn hX α hα hout S =>
    KFacts.exists_ne_of_sylow_of_isoLThreeMinusPi hn hX α hα hout S

theorem lThreeMinusPiInverting : LThreeMinusPiInverting :=
  fun _ _ _ _ hn hX α hα hout x hx3 hx1 hxα =>
    KFacts.exists_inverting_of_isoLThreeMinusPi hn hX α hα hout x hx3 hx1 hxα

theorem lStarTransvection_of_item97 (h97 : Sec9.Item97) : LStarTransvection :=
  lStarTransvection_of h97 (lStarTransvectionL3_of h97 lThreeMinusPiNoFixedSylow)

theorem lStarInverting_of_item97 (h97 : Sec9.Item97) : LStarInverting :=
  lStarInverting_of h97 (lStarInvertingL3_of h97 lThreeMinusPiInverting)

theorem item117_of_item97 (h97 : Sec9.Item97) (h112 : Item112) (h113 : Item113)
    (h116 : Item116) : Item117 :=
  item117_of_item113 h97 h112 h113 h116 lThreeMinusPiNoFixedSylow lThreeMinusPiInverting

end CFSG.RankThree.PartTwo.Sec11
