module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Main
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Aut5
public import CFSG.RankThree.PartTwo.Sec21.FF79JL5

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

theorem ff79_4_3_of
    (_h13 : FF79_1_3) (h14 : FF79_1_4) (h41 : FF79_4_1) (h42 : FF79_4_2Pre) : FF79_4_3 :=
  ff79_4_3_of_K ff79KO2L5_holds ff79KAut5Fix_holds ff79_JL5_holds h14 h41 h42

theorem ff79_4_2_of
    (h14 : FF79_1_4) (h41 : FF79_4_1) (h42 : FF79_4_2Pre) (h43 : FF79_4_3) : FF79_4_2 :=
  ff79_4_2_of_K ff79_JL5_holds h14 h41 h42 h43

end CFSG.RankThree.PartTwo.Sec21.FF79
