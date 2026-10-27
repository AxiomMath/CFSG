module

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

@[expose] def ruZ0Word : List (Fin 7 × Bool) :=
  [(2, true), (1, true), (2, false), (1, true), (0, true), (0, true)]

@[expose] def ruA0Words : List (List (Fin 7 × Bool)) :=
  [[(2, true), (1, true), (2, false), (1, true), (0, true), (0, true)],
   [(0, true), (2, true), (0, true), (2, true)],
   [(3, true), (2, false), (0, true), (3, true), (2, false), (0, true)]]

@[expose] def ruE0Words : List (List (Fin 7 × Bool)) :=
  [[(2, true), (1, true), (2, false), (1, true), (0, true), (0, true)],
   [(0, true), (2, true), (0, true), (2, true)],
   [(2, true), (0, false), (3, true), (0, true), (2, false), (3, true)],
   [(2, true), (0, false), (3, true), (1, true), (3, true), (2, true), (0, true)],
   [(2, false), (0, false), (2, false), (0, true)],
   [(0, false), (3, true), (1, true), (3, true), (1, true), (0, true)]]

end CFSG.ComponentClassification.GMS78.RuAsm
