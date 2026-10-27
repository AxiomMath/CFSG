module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure Setting13 (D : Data G) : Prop where
  sig_eq : D.sig = D.sig1
  hyp131 : F13.Hyp131 D

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
