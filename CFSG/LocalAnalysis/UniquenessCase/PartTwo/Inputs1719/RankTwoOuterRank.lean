module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.LocalAnalysis.UniquenessCase.UC22 (calC Bar2 Opp)
open CFSG.Blueprint (LieModel)

@[expose] def K_RankTwoOuterRank : Prop :=
  ∀ {H : Type} [Group H] [Finite H] (M L : Subgroup H) (n r : ℕ),
    L ∈ calC M →
      (LieModel (Bar2 L) .PSU 4 2 n ∨ LieModel (Bar2 L) .PSp 2 2 n ∨
        LieModel (Bar2 L) .G2 0 2 n) →
      r.Prime → 5 < r → r ∣ 2 ^ n - 1 → L ≠ Opp r M →
        3 ≤ CFSG.Open.pRank r M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
