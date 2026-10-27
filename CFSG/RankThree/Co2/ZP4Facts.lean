module

public import CFSG.RankThree.Co2.CrConj

public section

namespace CFSG.RankThree.Co2

@[expose] def ZP4Facts : Prop :=
  Nat.card (matGrp pWords4) ≤ 2 ^ 15 → ∀ x ∈ matGrp pWords4,
    (∀ y ∈ matGrp pWords4, x * y = y * x) → ¬ CrConj (repMat 2) x ∧ ¬ CrConj (repMat 7) x

end CFSG.RankThree.Co2

end
