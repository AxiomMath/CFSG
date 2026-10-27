module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofWitnessD4

public section

namespace CFSG.RankThree.PartTwo.Sec4

section ClassesD4

theorem inputs47ClassesD4_holds : Inputs47ClassesD4 :=
  Sec8.inputs47ClassesD4_of_lang Sec8.kF82D4LangCoset_holds Sec8.kF82D4SecondCent_holds

end ClassesD4

section Full

theorem rank3II_4_7_of_46 (h46 : Item4_6) : Item4_7 :=
  rank3II_4_7_of_d4 h46 inputs47WitnessD4_holds inputs47ClassesD4_holds

end Full

end CFSG.RankThree.PartTwo.Sec4
