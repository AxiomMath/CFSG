module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Fixed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R8105At (D : Data G) (L P : Subgroup G) (n : ℕ) : Prop :=
  ∀ B : Subgroup G, F08.NotationB8103 L P n B →
    ∀ H ∈ PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B),
      UniqueMax D.M H

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
