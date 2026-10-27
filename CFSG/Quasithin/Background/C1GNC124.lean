module

public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Statement

variable {G : Type} [Group G] [Finite G]

@[expose] def C124Statement : Prop :=
  ∀ (X T V L R : Subgroup G) (m : ℕ), CharTwo X → IsTwoReducedIn X V → IsSylowTwoOf T X →
    (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) → L ∈ cComp X → CharTwo L → ⁅V, L⁆ ≠ ⊥ →
    IsAltQuotient L (oTwoZIn L) m → pCoreOf 2 X ≤ R → R ≤ T →
    (m = 5 ∨ m = 7 ∨ (m = 6 ∧ R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G))) ∨
      (m = 6 ∧ Nat.card ↥(autOn R V) = 2)) →
    (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R ∧ (C.subgroupOf (baum R)).Characteristic ∧
        X ≤ Subgroup.normalizer (C : Set G)) ∨
      IsChiBlock X L ∨
      (IsBlock2 X L ∧ (IsExcA7Block L ∨ IsAltBlockType L 6 ∨ IsHatA6Block L))

end Statement

end CFSG.Quasithin
