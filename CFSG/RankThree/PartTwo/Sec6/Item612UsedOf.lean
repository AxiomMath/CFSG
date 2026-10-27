module

public import CFSG.RankThree.PartTwo.Sec6.Item612Used
public import CFSG.RankThree.PartTwo.Sec6.Item66Used
import CFSG.RankThree.PartTwo.Sec6.Item65Used

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem rank3II_6_12_sec21_of_used (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) : Sec21.Item612 :=
  rank3II_6_12_sec21Used h45 h49 (rank3II_6_5Used h45 h48 h49) (rank3II_6_8_of_used h45 h48 h49 hKf)

theorem rank3II_6_12_of_used (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) : Item6_12 :=
  rank3II_6_12Used h45 h49 (rank3II_6_5Used h45 h48 h49) (rank3II_6_8_of_used h45 h48 h49 hKf)

end CFSG.RankThree.PartTwo.Sec6
