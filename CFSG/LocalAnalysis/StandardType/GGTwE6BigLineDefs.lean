module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRowR3Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1Transport
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2Two
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LineAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.SCFourCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

@[expose] def GGTwE6BigLineLabels :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 4 → (∀ c, σ c = c ^ 2) →
    ∀ h : twistedE6InndiagGL K σ, h ≠ 1 → h ^ 3 = 1 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), CFSG.Open.IsElemAbelian 3 E →
      3 ^ 4 ≤ Nat.card E → twistedE6InndiagConj K σ h ∈ E →
      E ≤ (twistedE6InndiagConj K σ).range →
      E6AdToral (((E.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))) →
      ∀ J : Subgroup (twistedE6RootGroup K σ),
        CFSG.Open.IsComponentOf J
          (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
        LargeEvenMarking ↥J fun lab' _ _ _ _ _ => GGTwE6BigLabel lab'

@[expose] def GGTwE6BigThreeA2 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 4 → (∀ c, σ c = c ^ 2) →
    ∀ h : twistedE6InndiagGL K σ, h ≠ 1 → h ^ 3 = 1 → twE6MatFixDim K σ h = 24 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), CFSG.Open.IsElemAbelian 3 E →
      3 ^ 4 ≤ Nat.card E → twistedE6InndiagConj K σ h ∈ E →
      E ≤ (twistedE6InndiagConj K σ).range →
      E6AdToral (((E.comap (twistedE6InndiagConj K σ)).map
        (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))) →
      ∀ J : Subgroup (twistedE6RootGroup K σ),
        CFSG.Open.IsComponentOf J
          (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
        False

@[expose] def GGTwE6BigA4A1 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 4 → (∀ c, σ c = c ^ 2) →
    ∀ h : twistedE6InndiagGL K σ, h ≠ 1 → h ^ 3 = 1 → twE6MatFixDim K σ h = 28 →
    ∀ J : Subgroup (twistedE6RootGroup K σ),
      CFSG.Open.IsComponentOf J
        (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
      LargeEvenMarking ↥J fun lab' _ _ _ _ _ => lab' = ⟨.twA, 4, 1⟩

@[expose] def GGTwE6BigD5 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 4 → (∀ c, σ c = c ^ 2) →
    ∀ h : twistedE6InndiagGL K σ, h ≠ 1 → h ^ 3 = 1 → twE6MatFixDim K σ h = 46 →
    ∀ J : Subgroup (twistedE6RootGroup K σ),
      CFSG.Open.IsComponentOf J
        (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
      LargeEvenMarking ↥J fun lab' _ _ _ _ _ => lab' = ⟨.twD, 5, 1⟩

end CFSG.StandardType

end
