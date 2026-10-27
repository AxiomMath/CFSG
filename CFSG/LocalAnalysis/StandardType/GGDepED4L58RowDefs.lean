module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4L58RowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → p = 3 →
    Nat.card ↥Bs = 3 ^ 6 →
    (x ∉ L → y ∉ K → (k = 1 ∨ k = 2) → GGDepED4Aligned p k Bs L J K →
      GGResRowAt ggRowTwoNodeSmallJD p J L → (k = 2 → GGResRowAt ggRowTwoNode p J K) →
      GGTWHLAt p Bs L x ∧ GGTWHLAt p Bs K y) ∧
    (y ∉ K → GGDepED4Aligned p 1 Bs K J L → GGResRowAt ggRowTwoNodeSmallJD p J K →
      GGTWHLAt p Bs L x ∧ (Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
        GGTWHLAt p Bs K y))

end CFSG.StandardType

end
