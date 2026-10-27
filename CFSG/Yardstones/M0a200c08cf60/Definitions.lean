module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeF4
public import CFSG.LieType.SeitzGeneration.ExcOuterSplit
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCoreThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOutTower
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.Yardstones.M0a200c08cf60

open CFSG.LieType.SeitzGeneration

@[expose] def TwistedE6TypeBound :
    Prop :=
  ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
    CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TwTypeBoundStmt hf K hK σ hσ

structure TrialityPhi6Placements :
    Prop where
  ge5 : ∀ r : ℕ, 5 ≤ r → CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6PlacementSome r
  three : ∀ r : ℕ, 5 ≤ r → CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.Phi6PlacementSomeThree r

structure ExcAnisotropicF4Residuals : Prop where
  f4Phi3 : SeitzExcAnisotropicF4Class 3
  f4Phi6 : SeitzExcAnisotropicF4Class 6

structure ExcAnisotropicE6E8Residuals : Prop where
  e6Phi6 : SeitzExcAnisotropicE6Class 6
  e8Phi5 : SeitzExcAnisotropicE8Class 5
  e8Phi10 : SeitzExcAnisotropicE8Class 10
  e8Phi12 : SeitzExcAnisotropicE8Class 12

structure ExcAnisotropicThreeResiduals : Prop where
  trialityThree : SeitzExcAnisotropicTrialityThree
  reeF4Three : SeitzExcAnisotropicReeF4Three

structure ExcOuterLeOneResiduals : Prop where
  f4LeOne : SeitzExcOuterNarrowF4LeOne
  e6LeOne : SeitzExcOuterNarrowE6LeOne
  e7LeOne : SeitzExcOuterNarrowE7LeOne
  e8LeOne : SeitzExcOuterNarrowE8LeOne
  twistedE6LeOne : SeitzExcOuterNarrowTwistedE6LeOne

@[expose] def P1OffCharNonNormalRest : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (∀ (m : ℕ) (q : TauCeti.PrimePower), d.1 ≠ .A m q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .E6 q) → (∀ q : TauCeti.PrimePower, d.1 ≠ .E7 q) →
    CFSG.AGLEmbedding.P1OffCharAlmostSimpleNonNormalAt d

end CFSG.Yardstones.M0a200c08cf60
