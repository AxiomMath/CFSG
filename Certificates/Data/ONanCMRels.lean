module

public import Init

public section

namespace CFSG.OddStandard.ONanRec.CM

@[expose] def cmRelWords : List (List (Fin 6 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
   [(3, true), (3, true)], [(4, true), (4, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
   [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)],
   [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true),
    (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
   [(0, true), (2, true), (0, true), (2, true)], [(0, true), (3, true), (0, true), (3, true)],
   [(0, true), (4, true), (0, true), (4, true)], [(1, true), (3, true), (1, true), (3, true)],
   [(1, true), (4, true), (1, true), (4, true)], [(2, true), (4, true), (2, true), (4, true)],
   [(3, true), (4, true), (3, true), (4, true)],
   [(5, true), (5, true), (5, true), (5, true)],
   [(4, false), (0, false), (5, true), (5, true)],
   [(4, false), (0, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true),
    (2, true), (3, true)],
   [(2, true), (5, false), (3, false), (5, false), (3, false), (2, true), (3, true), (5, true),
    (3, true), (5, true)],
   [(3, true), (5, false), (2, false), (5, false), (2, false), (3, true), (2, true), (5, true),
    (2, true), (5, true)],
   [(1, true), (2, true), (3, true), (5, true), (1, true), (2, true), (3, true), (5, true),
    (1, true), (2, true), (3, true), (5, true), (1, true), (2, true), (3, true), (5, true),
    (1, true), (2, true), (3, true), (5, true)],
   [(5, true), (1, true), (2, false), (5, true), (2, true), (1, false), (5, true), (1, true),
    (2, false), (5, true), (2, true)],
   [(4, false), (3, true), (5, true), (3, true), (5, true), (3, true), (5, true), (3, true),
    (5, true)]]

end CFSG.OddStandard.ONanRec.CM
