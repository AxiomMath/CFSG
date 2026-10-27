module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

@[expose] def Asch511SmallLie (X : Type) [Group X] (r : ℕ) : Prop :=
  CFSG.Blueprint.LieModel X .G2 0 r 1 ∨ CFSG.Blueprint.LieModel X .PSp 2 r 1 ∨
    CFSG.Blueprint.LieModel X .PSL 3 r 1 ∨ CFSG.Blueprint.LieModel X .PSU 3 r 1

end CFSG.LocalAnalysis.WeakClosure81
