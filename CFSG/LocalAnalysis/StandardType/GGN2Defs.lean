module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRegimeN2 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ _ => p = 3 ∧ n = 3 ^ 5 ∧ labJ = ⟨.twA, 3, 1⟩

@[expose] def GGPairN2 (p : ℕ) (labL labJ : LargeEvenLabel) : Prop :=
  p = 3 ∧ labL = ⟨.D, 4, 1⟩ ∧ labJ = ⟨.twA, 3, 1⟩

@[expose] def GGRegimeN2L :
    ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labL labJ _ => p = 3 ∧ n = 3 ^ 5 ∧ labL = ⟨.D, 4, 1⟩ ∧ labJ = ⟨.twA, 3, 1⟩

@[expose] def GGRegimeN2RA : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ labX => GGRegimeN2 p n labJ labX ∧ GGKacRA labX p

@[expose] def GGN2ExcPairRK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeN2 p n labJ labX ∧ GGKacExcPair labX p

end CFSG.StandardType

end
