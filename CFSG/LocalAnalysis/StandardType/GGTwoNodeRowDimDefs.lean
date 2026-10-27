module

public import CFSG.LocalAnalysis.StandardType.GGResRows
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTwoNodeRowDimKnown : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J K →
    p ≠ 2 → 5 ≤ N → p ∣ N → Nat.card ↥Bs ≤ p ^ N

end CFSG.StandardType

end
