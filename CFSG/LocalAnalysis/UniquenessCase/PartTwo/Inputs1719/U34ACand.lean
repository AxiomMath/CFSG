module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarConjShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)

@[expose] def K_U34ACand : Prop :=
  ∀ (X : Type) [Group X], IsU3 X 2 → ACandLe X 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
