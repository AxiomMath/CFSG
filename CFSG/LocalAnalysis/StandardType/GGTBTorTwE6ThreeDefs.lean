module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTBTorTwE6Three : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ ggTorM lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW 3 5 (ggTorM lab) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ R I

end CFSG.StandardType

end
