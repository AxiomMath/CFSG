module

public import Mathlib

public section

namespace CFSG.Quasithin.A94.He42Fin

open Equiv

@[expose] def Stab0 : Subgroup (Perm (Fin 5)) :=
  alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) (0 : Fin 5)

end CFSG.Quasithin.A94.He42Fin
