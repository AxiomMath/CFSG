module

public import CFSG.GH74.M12.HypGroup
public import CFSG.GH74.M12.Statements
public import CFSG.Quasithin.Recognition.M12AscCoxInputs

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

@[expose] def x6 : Perm (Fin 6) := swap 4 5 * swap 3 4

@[expose] def x16 : Perm (Fin 6) := swap 1 2 * swap 0 1

@[expose] def D6l : List (Perm (Fin 6)) :=
  [1, x6, x6 * x6, x16, x16 * x6, x16 * (x6 * x6), x16 * x16, x16 * x16 * x6,
    x16 * x16 * (x6 * x6)]

end CFSG.Quasithin
