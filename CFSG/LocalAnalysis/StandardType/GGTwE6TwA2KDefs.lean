module

public import CFSG.LocalAnalysis.StandardType.GGResTwA2Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Assembly

@[expose] def ModelRLab (lab : LargeEvenLabel) (P : Prop) (K : Type) [Field K] (n : ℕ) : Prop :=
  ∀ φ : MulAut (TwE6Delta.RecipeR K n), φ ∈ TwE6Delta.RecipeI K n → φ ^ 3 = 1 →
    ∀ J : Subgroup (TwE6Delta.RecipeR K n), CFSG.Assembly.IsComponentOf J (ggFixSub φ) →
      GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) →
        P ∧
          ∀ A : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 A → φ ∈ A →
            (∀ a ∈ A, a ∈ TwE6Delta.RecipeI K n) → Nat.card A ≤ 3 ^ 4

@[expose] def ModelR (K : Type) [Field K] (n : ℕ) : Prop :=
  ModelRLab ⟨.twA, 2, 3 * n⟩ (3 ∣ 2 ^ n + 1) K n

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Chevalley in
@[expose] def ModelAtLab
    (lab : LargeEvenLabel) (P : Prop) (K : Type) [Field K] (σ : K ≃+* K) (n : ℕ) : Prop :=
  ∀ h : ↥(twistedE6InndiagGL K σ), h ^ 3 = 1 → h ≠ 1 →
    ∀ J : Subgroup ↥(twistedE6RootGroup K σ),
      CFSG.Open.IsComponentOf J
          (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h)) →
        GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) →
          P ∧
            ∀ A : Subgroup ↥(twistedE6InndiagGL K σ), IsElemAbelian 3 A → h ∈ A →
              Nat.card A ≤ 3 ^ 4

@[expose] def ModelAt
    (K : Type) [Field K] (σ : K ≃+* K) (n : ℕ) : Prop :=
  ModelAtLab ⟨.twA, 2, 3 * n⟩ (3 ∣ 2 ^ n + 1) K σ n

end CFSG.StandardType.TwE6TwA2K

end
