module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Families
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Yardstones.M19b85589cdfc

@[expose] def Gls3PlusReeG2 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (m : ℕ), d.1 = .reeG2 m →
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3PlusCase (.lie d)

@[expose] def TwistedE6TypeBound :
    Prop :=
  ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
    CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TwTypeBoundStmt hf K hK σ hσ

@[expose] def D1RankFourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
      CFSG.Open.GLBPreuniqueness G →
      ∀ (p : ℕ), p ∈ CFSG.Open.GLBBetaFour G → ∀ (P : Sylow p G) (M : Subgroup G),
        CFSG.Open.GLBIsMaxTwoLocal M → CFSG.Open.GLBWeakCore p (P : Subgroup G) ≤ M →
          ∀ (H : Subgroup G), CFSG.Open.IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M

end CFSG.Yardstones.M19b85589cdfc
