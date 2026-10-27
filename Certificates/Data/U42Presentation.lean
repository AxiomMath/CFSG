module

public section

namespace CFSG.HardMathSupport.Dickson.I271.U42Presentation

@[expose] def u42Words : List (List (Fin 2 × Bool)) :=
  [[(0, true), (0, true)],
    List.flatten (List.replicate 5 [(1, true)]),
    List.flatten (List.replicate 9 [(0, true), (1, false)]),
    List.flatten (List.replicate 2
      [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true)]),
    List.flatten (List.replicate 3 [(1, false), (0, true), (1, true), (0, true)])]

end CFSG.HardMathSupport.Dickson.I271.U42Presentation
