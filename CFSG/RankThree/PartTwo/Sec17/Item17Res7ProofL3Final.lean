module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofOne
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3W
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Aut
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoK

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

section Provers

theorem claim1718QuotOneL3_proof (h1715 : Item1715) (h135 : Item135) (h142 : Concl142S14)
    (h9 : CardInfNineS17) (h138 : Item138N) : Claim1718QuotOneL3 :=
  claim1718QuotOneL3_of_autCent ks17L3AutCent h1715 h135 h142 h9 h138

theorem claim1719WNJOneL3_proof (h1715 : Item1715) (h135 : Item135) (h142 : Concl142S14)
    (h9 : CardInfNineS17) (h138 : Item138N) : Claim1719WNJOneL3 :=
  claim1719WNJOneL3_of_autCent ks17L3AutCent ks17L3TwoCent h1715 h135 h142 h9 h138

theorem item1717OneL3J2_proof
    (hJ : KS1717J2Inner)
    (hJC : Item1717OneJ2Clause) (h1715 : Item1715) (h135 : Item135) (h142 : Concl142S14)
    (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17) (h9 : CardInfNineS17)
    (h138 : Item138N) : Item1717OneL3J2 :=
  item1717OneL3J2_of ks17L3AutCent ks17L3TwoCent hJ hJC h1715 h135 h142 h166 hbot h168 h9 h138

end Provers

end CFSG.RankThree.PartTwo.Sec17
