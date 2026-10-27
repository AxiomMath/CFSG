module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTPNClTag (t : LargeEvenLieTag) : Prop :=
  t = .A ∨ t = .twA ∨ t = .B ∨ t = .C ∨ t = .D ∨ t = .twD

@[expose] def GGTPNExcTag (t : LargeEvenLieTag) : Prop :=
  t = .F4 ∨ t = .E6 ∨ t = .twE6 ∨ t = .E7 ∨ t = .E8

@[expose] def GGClGenRK (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  GGTablePKnownRK fun p n labJ labX => R p n labJ labX ∧ GGKacGenericCl labX p

@[expose] def GGNonExcRK (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    R p n labJ labX ∧ ¬ GGTPNClTag labX.tag ∧ ¬ GGTPNExcTag labX.tag


end CFSG.StandardType

end
