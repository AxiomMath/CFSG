module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporAll
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSeven

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem k423InnerCensus_of_res2
    (h3 : K423Inner46Three) (hθ : K423SporThetaCent) (hJ3 : K423SporJ3) (hJ4 : K423SporJ4)
    (hMcL : K423SporMcL) (h6 : K423Inner46SixRest) (hθ7 : K423ThetaCentSeven)
    (hSp : K423SevenSp62) (h8 : K423Inner46EightRest) : K423InnerCensus :=
  k423InnerCensus_of_spor h3 hθ hJ3 hJ4 hMcL h6 (k423Inner46Seven_of hθ7 hSp)
    (k423Inner46Eight_of h8)

end CFSG.RankThree.PartTwo.Sec4
