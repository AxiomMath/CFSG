module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def LnTwoNoBender : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X) →
    ∀ U K : Subgroup X, IsSylowTwoOf U ⊤ → U ≤ Subgroup.normalizer (K : Set X) → K ⊔ U ≠ ⊤ →
      ¬ ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K)

@[expose] def Core3HeLnTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CharTwo (S1421.g0Of T M H K1) →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → yOfL22 T M ≤ L →
        (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) → False

@[expose] def Core3HeA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CharTwo (S1421.g0Of T M H K1) →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → yOfL22 T M ≤ L →
        IsAlt 7 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) → False

end CFSG.Quasithin
