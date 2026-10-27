module

public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensusAlt
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA6
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA7
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA8
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA9

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem k423Inner46FourAlt : K423Inner46FourAlt := by
  rintro X _ _ ⟨n, h6, h9, ⟨e⟩⟩ - - -
  interval_cases n
  · exact Res423Two.census423_of_alt6 e
  · exact Res423Two.census423_of_alt7 e
  · exact Res423Two.census423_of_alt8 e
  · exact Res423Two.census423_of_alt9 e

end CFSG.RankThree.PartTwo.Sec4
