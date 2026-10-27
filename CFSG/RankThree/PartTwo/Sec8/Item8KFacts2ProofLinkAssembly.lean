module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLink
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee

public section

namespace CFSG.RankThree.PartTwo.Sec8


theorem kF84Field_of_list
    (h82 : Item86ResProof.Item82TwoList) : KF84Field :=
  kF84Field_of_inputs h82 (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
    kF84FieldRee_holds

theorem kF87Link_of_list
    (h82 : Item86ResProof.Item82TwoList) (h84 : Pair84A) : KF87Link :=
  kF87Link_of (kF84Field_of_list h82) (kF87LinkOne_of h84)

end CFSG.RankThree.PartTwo.Sec8
