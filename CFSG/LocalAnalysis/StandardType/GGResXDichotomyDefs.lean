module

public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResXDichotomyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
      (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K)

end CFSG.StandardType

end
