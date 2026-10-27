module

public import CFSG.Foundations.Catalog
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

@[expose] def KF207ThetaTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Θ L : Subgroup G), CFSG.IsKGroup ↥Θ →
    Nat.Coprime 3 (Nat.card Θ) → (∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p Θ ≤ 2) →
    L ≤ Subgroup.normalizer (Θ : Set G) → ⁅L, L⁆ = L →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)) →
    ⁅L, Θ⁆ ≤ CFSG.Open.pCoreOf 2 Θ

end CFSG.RankThree.PartTwo.Sec20
