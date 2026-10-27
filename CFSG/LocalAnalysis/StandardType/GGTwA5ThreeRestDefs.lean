module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBWeylRowResRest (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTBWeylRowRes p lab ∧ ¬ (lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)

@[expose] def GGTBXDatumResInputRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGInnerDiagOnLabel GGTBWeylRowResRest p Bs L → GGResXDatum p Bs L) ∧
      (GGInnerDiagOnLabel GGTBWeylRowResRest p Bs K → GGResXDatum p Bs K)

end CFSG.StandardType

end
