module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec4

theorem item4_19NJ3_of_res2_types
    (h417 : Item4_17) (h46 : Item4_6) (hAut : K419AutThree) (hOne : K419OneField)
    (hU4 : K419U4Odd) (hC : K419UnitaryCensus) : Item4_19NJ3 :=
  item4_19NJ3_of_census h417 h46 (k419E27_of_autThree hAut) hOne hU4 hC

theorem item4_19NJ3_of_res2_census
    (h417 : Item4_17) (h46 : Item4_6) (hAut : K419AutThree) (hOne : K419OneFieldCensus)
    (hU4 : K419U4Odd) (hC : K419UnitaryCensus) : Item4_19NJ3 :=
  item4_19NJ3_of_res2_types h417 h46 hAut (k419OneField_of h46 hOne) hU4 hC

end CFSG.RankThree.PartTwo.Sec4
