module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGE6KGLayerInputTw : Prop :=
  ∀ lab : LargeEvenLabel, lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGE6KGLayers R I

end CFSG.StandardType

end
