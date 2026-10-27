module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinalDefs
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofU43
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofMcL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.RankThree.OddKernel.EightGroupDims
public import CFSG.RankThree.PartOne.S10.PlaneLocalRankContract
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLUsed
public import Certificates.Certificate8058
public import Certificates.Certificate8059

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem e81U43_holds : E81U43 := by
  obtain ⟨P, -, -, hP, hP81, -⟩ := Res417Five.k417E81U43_holds
  exact ⟨P, hP, by norm_num [hP81]⟩

theorem e81McL_holds : E81McL := by
  obtain ⟨P, -, -, hP, hP81, -⟩ := Res417Five.k417E81McL_holds
  have h81 : 81 ≤ Nat.card P := by norm_num [hP81]
  exact ⟨P, hP, h81⟩

theorem e81ON_holds : E81ON := by
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
  exact ⟨E, hE, by norm_num [hc]⟩

end CFSG.RankThree.PartTwo.Sec4
