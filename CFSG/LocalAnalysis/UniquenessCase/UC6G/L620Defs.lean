module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

abbrev Lbar : Type := ↥m.L ⧸ CFSG.pPrimeCore m.r ↥m.L

@[expose] def L620 : Prop :=
  m.C620 ∧ (LieModel m.Lbar .PSL 2 m.r 2 ∨
    (m.r = 3 ∧ (IsSpor m.Lbar .M11 ∨ LieModel m.Lbar .PSL 3 2 2)) ∨
    (m.r = 5 ∧ (LieModel m.Lbar .Tits 0 2 1 ∨ IsAlt m.Lbar 10)))

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
