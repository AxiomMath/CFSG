module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Bridge
public import CFSG.RankThree.PartTwo.Sec21.FF79JL5
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44Bi
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44Z
import CFSG.RankThree.PartTwo.Sec21.FF79KFactsSmall
import CFSG.RankThree.PartTwo.Sec21.FF79KFactsL3Z
import CFSG.RankThree.PartTwo.Sec21.FF79KTransvZ
import CFSG.RankThree.PartTwo.Sec21.FF79KOneSix
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

theorem ff79_4_4X_of_lemmas
    (h41 : FF79_4_1) (h42 : FF79_4_2) (h43 : FF79_4_3) : FF79_4_4X := by
  have hstr := ff79_4_3Str_of h41 h42 h43 ff79_JL5_holds
  have hβ := ff79_4_4Beta_of hstr ff79KCentA5_holds ff79KCentL3_holds
  exact ff79_4_4X_of ff79_1_6_holds ff79_JL5_holds
    (ff79_4_4J_of hstr ff79KCentA5_holds ff79KAutL5_holds (ff79_KleJ_of h41 h43)) hβ
    (ff79_4_4Z_of hstr hβ ff79KCentA5_holds ff79KCentL3NonAb_holds ff79KTransvComm_holds
      ff79KTransvCenter_holds)
    (ff79_4_4Bi_of hstr ff79KTransvL5_holds)

end CFSG.RankThree.PartTwo.Sec21.FF79
