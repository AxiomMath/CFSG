module


public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

@[expose] def K_Asch511SylowOvergroupsPSp4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r : ℕ), r.Prime → r ≠ 2 →
    CFSG.Blueprint.LieModel X .PSp 2 r 1 →
    ∀ (P : Sylow 2 X) (Y : Subgroup X), (P : Subgroup X) ≤ Y → Y < ⊤ →
      ¬ HasCompFactor Y IsCalL0

end CFSG.LocalAnalysis.WeakClosure81

end
