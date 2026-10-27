module

public import Mathlib.Logic.Equiv.Defs

public section

namespace CFSG.Quasithin.H13

open Equiv

abbrev Pres56 (σ : Perm (Fin 7)) : Prop := (σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5)

end CFSG.Quasithin.H13
