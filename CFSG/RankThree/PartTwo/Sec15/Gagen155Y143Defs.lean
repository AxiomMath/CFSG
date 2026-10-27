module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def Is143Point {Y : Type*} [Group Y] (x : Y) : Prop :=
  x ^ 3 = 1 ∧ x ∉ Subgroup.center Y ∧
    (∀ u : Y, u * x = x * u → u ^ 3 = 1 → u ∈ Subgroup.zpowers x ⊔ Subgroup.center Y) ∧
    ∀ z ∈ Subgroup.center Y, ∀ g : Y, g * x * g⁻¹ = x * z → z = 1

@[expose] def K143Excl : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SectionFourHyp Y → CFSG.IsQuasisimple Y →
    Nat.card (Subgroup.center Y) = 3 → ∀ x : Y, ¬ Is143Point x

end CFSG.RankThree.PartTwo.Sec15
