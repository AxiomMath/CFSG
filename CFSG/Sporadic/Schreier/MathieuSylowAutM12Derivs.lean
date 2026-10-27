module

public import Init

public section

namespace CFSG.Sporadic.Schreier

@[expose] def m12Derivs : List (List Int) :=
  [[-2, 1, 2], [1, -2, 1, 2, 1], [-2, -2, 1, 2, 2], [3, 5, 3], [3, 4, 5, 4], [-7, 6, 7, 6, 7],
    [6, -7, 6, 7, 7, 7], [-8, -8, 9, 8], [9, 8, 9]]

end CFSG.Sporadic.Schreier

end
