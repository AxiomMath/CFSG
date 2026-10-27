module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.WeakClosure81.W15Seven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1)

variable {G : Type} [Group G] [Finite G]

theorem NormalizersInM.toTwo {V H W : Subgroup G} (h : NormalizersInM V H W) :
    NormalizersInMTwo V H W :=
  fun X hX _ hXN hNX => h X hX hXN hNX

end CFSG.LocalAnalysis.WeakClosure81

end
