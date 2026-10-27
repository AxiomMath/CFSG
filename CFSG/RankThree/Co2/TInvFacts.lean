module

public import CFSG.RankThree.Co2.CrConj
public import CFSG.RankThree.Co2.CensusData

public section

namespace CFSG.RankThree.Co2

@[expose] def TInvFacts : Prop :=
  Nat.card (matGrp sylWords) ≤ 2 ^ 18 →
    ∀ x ∈ matGrp sylWords, x * x = 1 → x ≠ 1 → ∃ i < 10, CrConj (repMat i) x

end CFSG.RankThree.Co2

end
