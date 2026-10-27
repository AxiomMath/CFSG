module

public import Init

public section

namespace CFSG.Sporadic.Schreier

@[expose] def m22Derivs : List (List Int) :=
  [[1, -2, -2, 1, 2, 2, 1], [1, -2, 1, -2, 1, 2, 1, 2], [3, 4, 3], [-4, 3, 4],
    [-2, -2, 1, 2, 1, 2, 2], [-5, 6, -4, -7, -4, 3, 4, 7, 3], [-5, -5, -8, 5, 6, 5],
    [-8, -8, 9, 6, 5, 8, 5]]

end CFSG.Sporadic.Schreier

end
