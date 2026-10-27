module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJYFactsL2
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJYFactsU3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree.PartTwo.Sec15

theorem res1HJYFacts_of_res1OpenType {Y : Type} [Group Y] (hY : Res1OpenType Y) :
    Res1HJYFacts Y := by
  rcases hY with ⟨n, hn0, h4, ⟨e⟩⟩ | ⟨n, hn0, hn, ⟨e⟩⟩
  · exact Res1HJYFacts.of_mulEquiv e (res1HJYFacts_projSL hn0 h4)
  · exact Res1HJYFacts.of_mulEquiv e (res1HJYFacts_projSU hn0 hn)

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
