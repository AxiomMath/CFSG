module

public import CFSG.RankThree.PartOne.N1322.Core
public import CFSG.RankThree.PartOne.N1322.Bridge3

public section

namespace CFSG.RankThree.PartOne.N1322

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem node1322_of_cases (hres : PrimitiveResidual)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hPairJ : NF7J.PairMember) (hOdd : KF1322Odd) (hKty : KF1322Kty) (hG2 : KF1322G2)
    (hNF7U : NF7H.KF1322NF7U) : Node1322 := by
  intro G _ _ p A c L E h12 hF12 hF13 hT hEA hL
  have : Fact p.Prime := ⟨h12.prime⟩
  obtain ⟨d, hd, hconcl⟩ := bridge hGA h12 hF12 hF13 hT hEA hL hOdd hKty hG2 hPairJ hNF7U
  obtain ⟨hn, e⟩ := core_main hres hd
  exact hconcl hn e

end CFSG.RankThree.PartOne.N1322
