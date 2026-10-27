module

public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step13PZeroCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ P₀ : Subgroup G, c ∈ P₀ → P₀ ≤ Sec4.thetaQuotCentralizer L →
      CFSG.Assembly.IsElemAbelian 3 P₀ → Nat.card P₀ = 9 → False

end CFSG.RankThree.PartTwo.Sec13
