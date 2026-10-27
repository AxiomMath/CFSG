module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Toral

@[expose] def IsToralSubgroup (τ : Tag) (L : Type) [Field L] (A : Subgroup (ModGL τ L)) : Prop :=
  ∃ g ∈ adjointGroup τ L, ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ L

end Toral

end ExcFramesHalf

end CFSG.StandardType
