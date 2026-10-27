module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open

namespace UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

@[expose] def C631 : Prop := ⁅m.A ⊓ m.L, m.K⁆ ≤ m.U

end Mz614

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
