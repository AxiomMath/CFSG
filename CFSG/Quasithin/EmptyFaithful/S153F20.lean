module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G] [Finite G]

@[expose] def C27OneTwo (K R V : Subgroup G) : Prop :=
  (pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ∧
    (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
    IsTwoReducedIn (K ⊔ R) V) ∧
  (¬ thompsonJ R ≤ thompsonJ (pCoreOf 2 (K ⊔ R)) ∧
    ∃ hV : IsElemAbelian 2 V,
      @IsFFModule V (commGroupOfElemAbelian hV) (autOn (K ⊔ R) V) ∧
      ∃ A : Subgroup (MulAut ↥V), A ≤ autOn R V ∧
        @IsFFStarOffender V (commGroupOfElemAbelian hV) (autOn (K ⊔ R) V) A)

end Vocabulary

@[expose] def SL3Sp4NotA38Type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), (IsSL3Quot L ∨ IsSp4Quot L) →
    ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def SolvOvergroupsInBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ X : Subgroup G), (IsSL3Quot L ∨ IsSp4Quot L) →
    IsSylowTwoOf S₀ L → S₀ ≤ X → X ≤ L → Group.IsSolvable ↥X →
      X ≤ Subgroup.normalizer (S₀ : Set G)

@[expose] def RankTwoMaxParabolics : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ : Subgroup G), (IsSL3Quot L ∨ IsSp4Quot L) →
    IsSylowTwoOf S₀ L →
      ∃ P₁ P₂ : Subgroup G, IsMaxParabolic2 L P₁ ∧ IsMaxParabolic2 L P₂ ∧ P₁ ≠ P₂ ∧
        L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P₁ ∧ L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P₂ ∧
        ∀ P : Subgroup G, IsMaxParabolic2 L P → L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P →
          P = P₁ ∨ P = P₂

end CFSG.Quasithin
