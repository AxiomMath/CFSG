module

public import Init

public section

namespace CFSG.OddStandard.ChengHeld.ONSylow

@[expose] def onRels : List (List (Fin 8 × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true)],
   [(1, true), (1, true)],
   [(2, true), (2, true), (2, true), (2, true)],
   [(3, true), (3, true)],
   [(4, true), (4, true)],
   [(5, true), (5, true)],
   [(6, true), (6, true)],
   [(2, true), (2, true), (0, false), (0, false)],
   [(1, false), (2, false), (1, true), (2, true)],
   [(3, false), (1, true), (3, true), (1, false), (0, false), (0, false)],
   [(4, false), (1, true), (4, true), (1, false), (0, false), (0, false)],
   [(5, false), (1, true), (5, true), (1, false), (0, false), (0, false)],
   [(4, false), (3, false), (1, true), (3, true), (4, true), (1, false)],
   [(6, false), (1, true), (6, true), (1, false)],
   [(6, false), (2, true), (6, true), (2, false), (0, false), (0, false)],
   [(4, false), (2, true), (4, true), (2, false), (0, false), (0, false)],
   [(5, false), (2, true), (5, true), (2, false), (0, false), (0, false)],
   [(2, false), (3, false), (2, true), (3, true)],
   [(3, false), (4, false), (3, true), (4, true)],
   [(5, false), (6, false), (5, true), (6, true)],
   [(3, false), (6, false), (3, true), (6, true), (2, false), (1, false)],
   [(3, false), (5, false), (3, true), (5, true), (1, false), (0, false)],
   [(4, false), (6, false), (4, true), (6, true), (2, false)],
   [(4, false), (5, false), (4, true), (5, true), (2, false), (1, false), (0, false)],
   [(7, true), (7, true)],
   [(7, false), (0, true), (7, true), (0, true)],
   [(7, false), (1, true), (7, true), (1, false)],
   [(7, false), (2, true), (7, true), (2, true), (1, false)],
   [(7, false), (3, true), (7, true), (5, false), (0, false), (0, false)],
   [(7, false), (4, true), (7, true), (6, false), (5, false)],
   [(7, false), (5, true), (7, true), (3, false), (0, false), (0, false)],
   [(7, false), (6, true), (7, true), (4, false), (3, false), (0, false), (0, false)]]

end CFSG.OddStandard.ChengHeld.ONSylow
