module

public import CFSG.RankThree.PartTwo.Sec4.Item49OddChar
public import CFSG.RankThree.PartTwo.Sec4.Item49Small
public import CFSG.RankThree.PartTwo.Sec4.Item49CharTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4


theorem inputs49 : Inputs49 where
  oddOThreePrime X _ _ hX hq := by
    rcases hX with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact oddOThreePrime_oddChar X (Or.inl h1) hq
    · exact oddOThreePrime_oddChar X (Or.inr (Or.inl h2)) hq
    · exact oddOThreePrime_oddChar X (Or.inr (Or.inr h3)) hq
    · exact oddOThreePrime_four X h4 hq
    · exact oddOThreePrime_five X h5 hq
    · exact oddOThreePrime_charTwo X (Or.inl h6) hq
    · exact oddOThreePrime_charTwo X (Or.inr h7) hq
    · exact oddOThreePrime_eight X h8 hq

end CFSG.RankThree.PartTwo.Sec4
