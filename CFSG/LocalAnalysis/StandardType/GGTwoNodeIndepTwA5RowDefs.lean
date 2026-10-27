module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTwoNodeIndepTwA5RowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    ∀ (X : Subgroup G) (z : G), (X = L ∧ z = x) ∨ (X = K ∧ z = y) →
      ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) →
        ggRowTwoNode p labJ labX → z ∈ X → p = 3 →
        (labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) → GGResXDatumAx p Bs X z 5

end CFSG.StandardType

end
