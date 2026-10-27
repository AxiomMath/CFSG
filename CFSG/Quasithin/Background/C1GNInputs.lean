
module

public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def C126Statement (C₁ C₂ : Subgroup G → Subgroup G) : Prop :=
  ∀ H T : Subgroup G, IsSQTKTC H → IsSylowTwoOf T H → CharTwo H → IsMinParabolicOf H H →
    C₁ T ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ T : Set G) ∨
      ∃ (r : ℕ) (K : Fin r → Subgroup G), 1 ≤ r ∧
        (∀ i, IsChi0Block H (K i) ∧ ⁅K i, thompsonJ T⁆ = K i) ∧
        (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H = ⨆ i, K i ∧
        (∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j) ∧
        (∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j)

@[expose] def C127Statement : Prop :=
  ∀ X T P K : Subgroup G, CharTwo X → IsSylowTwoOf T X → CFSG.SectionRank.IsKGroupCat ↥X →
    P ∈ uFamHat X T → IsBlock2 P K → ⁅K, thompsonJ T⁆ = K → P = T ⊔ conjClosure K T →
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n)

@[expose] def C123TwoStatement (C₁ C₂ : Subgroup G → Subgroup G) : Prop :=
  ∀ T R Y L : Subgroup G, IsPGroup 2 T → baum T ≤ R → R ≤ T → IsSylowTwoOf R Y → CharTwo Y →
    L ∈ cComp Y → (∀ y ∈ Y, ∃ l ∈ L, ∃ r ∈ R, y = l * r) → IsExcA7Block L →
      Y = (Y ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (C₂ T : Set G))

@[expose] def DistinctBlocksCommuteStatement : Prop :=
  ∀ H B₁ B₂ : Subgroup G, CharTwo H → IsBlock2 H B₁ → IsBlock2 H B₂ → B₁ ≠ B₂ → ⁅B₁, B₂⁆ = ⊥

@[expose] def BaumNormalizesChiBlocksStatement : Prop :=
  ∀ H T V L : Subgroup G, CharTwo H → IsTwoReducedIn H V → IsSylowTwoOf T H → IsChiBlock H L →
    ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G) →
      baum T ≤ Subgroup.normalizer (L : Set G)

@[expose] def AltBlockStatement : Prop :=
  ∀ X T L : Subgroup G, CharTwo X → IsSQTKTC X → IsSylowTwoOf T X → IsBlock2 X L →
    blockU L ≤ VZ T X → ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) →
    (∃ m : ℕ, Odd m ∧ IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m) →
      IsChiBlock X L ∨ IsExcA7Block L

end Statements

end CFSG.Quasithin
