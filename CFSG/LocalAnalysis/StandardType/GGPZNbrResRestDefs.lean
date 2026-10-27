module

public import CFSG.LocalAnalysis.StandardType.GGPZNbrRes
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGPZNbrResDatumRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∀ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y →
      J ≤ Y → Bs ≤ Subgroup.normalizer (Y : Set G) → GGNbr p B x D J (z : G) Y →
      GGInnerDiagOnLabel GGTBWeylRowResRest p Bs Y → GGResXDatumSurj p Bs Y

end CFSG.StandardType

end
