module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGNbrKGFieldG2ThreeOff : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .G2 → 6 ∣ lab.n →
    LargeEvenLabelAll lab (fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineFieldCompOff 3 2 R I F (ggG2SL3Card lab.n))

end CFSG.StandardType

end
