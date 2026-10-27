module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C622 : Prop :=
  CFSG.Open.IsQuasisimple ↥m.L ∨
    (m.r = 3 ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (↥m.L ⧸ CFSG.pPrimeCore m.r ↥m.L) 6)

variable {m}

theorem C622.quasisimple_of_ne_three (h : m.C622) (hr : m.r ≠ 3) : CFSG.Open.IsQuasisimple ↥m.L :=
  h.resolve_right fun h' => hr h'.1

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
