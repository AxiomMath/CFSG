module

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

@[expose] def p10Cox : List (List (Fin 7 × Bool)) :=
  [[(0, true), (0, true)],
   [(1, true), (1, true)],
   [(2, true), (2, true)],
   [(3, true), (3, true)],
   [(4, true), (4, true)],
   [(5, true), (5, true)],
   [(0, true), (1, true), (0, true), (1, true)],
   [(0, true), (2, true), (0, true), (2, true), (0, true), (2, true)],
   [(0, true), (3, true), (0, true), (3, true)],
   [(0, true), (4, true), (0, true), (4, true)],
   [(0, true), (5, true), (0, true), (5, true)],
   [(1, true), (2, true), (1, true), (2, true)],
   [(1, true), (3, true), (1, true), (3, true), (1, true), (3, true)],
   [(1, true), (4, true), (1, true), (4, true)],
   [(1, true), (5, true), (1, true), (5, true)],
   [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
   [(2, true), (4, true), (2, true), (4, true)],
   [(2, true), (5, true), (2, true), (5, true)],
   [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)],
   [(3, true), (5, true), (3, true), (5, true)],
   [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)]]

@[expose] def p10R1 : List (Fin 7 × Bool) := [(6, true), (6, true), (1, true)]

@[expose] def p10R2 : List (List (Fin 7 × Bool)) :=
  [[(6, true), (0, true), (6, true), (6, true), (6, true), (1, true), (0, true)],
   [(6, true), (4, true), (6, true), (6, true), (6, true), (1, true), (4, true)],
   [(6, true), (5, true), (6, true), (6, true), (6, true), (1, true), (5, true)]]

@[expose] def p10R3 : List (Fin 7 × Bool) :=
  [(6, true), (3, true), (1, true), (2, true), (3, true), (4, true), (5, true), (6, true),
   (3, true), (1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (3, true),
   (1, true), (2, true), (3, true), (4, true), (5, true)]

@[expose] def p10Ws : List (List (Fin 7 × Bool)) := p10Cox ++ [p10R1] ++ p10R2 ++ [p10R3]

end CFSG.Quasithin.H13.F431.U42Aut
