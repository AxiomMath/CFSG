module

public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Sporadic.Co1.Module.FormsBase

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (bil₀)

@[expose] def Co1EdgeFact : Prop :=
  ∀ s : Co1, orderOf s = 2 → ∀ a b : Fin 24 → ZMod 2, a ∈ co1Orbit 0 → b ∈ co1Orbit 0 →
    a + b ∈ co1Orbit 0 → co1Act s a = a → co1Act s b = b →
    (∀ x, co1Act s x = x → bil₀ a x = 0) → ∃ y, y + co1Act s y = b ∧ bil₀ a y = 1

end CFSG.Monster.GMS
