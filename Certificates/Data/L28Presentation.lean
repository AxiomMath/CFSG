module

public section

namespace CFSG.HardMathSupport.Dickson.I271.L28Presentation

@[expose] def l28Words : List (List (Fin 2 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true)],
    List.flatten (List.replicate 7 [(1, true), (0, true)]),
    [(1, true)] ++ List.flatten (List.replicate 3
      [(0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]) ++
      [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
        (0, true)]]

end CFSG.HardMathSupport.Dickson.I271.L28Presentation
