module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def GGE6DepPairBlock (p : ℕ) (Bs L : Subgroup G) (a b : ↥Bs) (Dv N : Subgroup G) :
    Prop :=
  IsComponentOf Dv (L ⊓ Subgroup.centralizer ({(a : G) * (b : G)} : Set G)) ∧
    (∀ D' : Subgroup G,
      IsComponentOf D' (L ⊓ Subgroup.centralizer ({(a : G) * (b : G)} : Set G)) → D' = Dv) ∧
    IsComponentOf N (L ⊓ Subgroup.centralizer ({(a : G), (b : G)} : Set G)) ∧
    (∀ N' : Subgroup G,
      IsComponentOf N' (L ⊓ Subgroup.centralizer ({(a : G), (b : G)} : Set G)) → N' = N) ∧
    N ≤ Dv ∧ IsCyclic (Subgroup.center N) ∧
    (∀ u : ↥Bs, u ∈ ggFixedByCentres p (ggAutomizer L Bs) {a, b} → (u : G) ∈ L → (u : G) ∈ N) ∧
    ∃ n ∈ Dv, n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * (a : G) * n⁻¹ ≠ (a : G)

end CFSG.StandardType

end
