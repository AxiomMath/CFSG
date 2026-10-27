module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Res1HJYFacts (Y : Type) [Group Y] : Prop :=
  (∀ U V : Sylow 2 Y, U ≠ V → (U : Subgroup Y) ⊓ V = ⊥) ∧
  (∀ U : Sylow 2 Y, ∀ y z : Y, y ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) →
    z ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) → orderOf y = 3 → orderOf z = 3 →
      z ∈ (U : Subgroup Y) ⊔ Subgroup.zpowers y) ∧
  (∀ U : Sylow 2 Y, ∀ y : Y, y ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) →
    orderOf y = 3 → ∃ t ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y),
      orderOf t = 5 ∧ Commute t y)

@[expose] def J2AutFixNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 → ∀ σ : MulAut X, Nat.Coprime 3 (orderOf σ) →
      (∀ e ∈ E, σ e = e) → σ = 1

@[expose] def J2HasE25 : Prop :=
  ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.J2, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 25

@[expose] def HJThetaS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L

end CFSG.RankThree.PartTwo.Sec15
