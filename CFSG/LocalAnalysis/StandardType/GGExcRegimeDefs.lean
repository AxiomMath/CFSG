module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGExcGenRK (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  GGTablePKnownRK fun p n labJ labX => R p n labJ labX ∧ GGKacGeneric labX p

end CFSG.StandardType

end
