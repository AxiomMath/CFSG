module

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.M13L33

@[expose] def la : Fin 2 × Bool := (0, true)

@[expose] def lb : Fin 2 × Bool := (1, true)

@[expose] def lB : Fin 2 × Bool := (1, false)

@[expose] def l33Rels : List (List (Fin 2 × Bool)) :=
  [[la, la],
    List.replicate 13 lb,
    (List.replicate 3 [la, lB]).flatten,
    (List.replicate 3 ([la] ++ List.replicate 2 lB ++ [la] ++ List.replicate 2 lb)).flatten,
    (List.replicate 2 ([la] ++ List.replicate 5 lB ++ [la] ++ List.replicate 5 lb)).flatten]

end CFSG.HardMathSupport.Dickson.BMRows.M13L33
