module

public import Init

public section

namespace CFSG.Sporadic.Schreier

@[expose] def m23Derivs : List (List Int) :=
  [[-2, -2, 1, 2, 2], [1, -2, 1, 2, 1, 2, 1], [4, 4], [3, -4, 3, -4, 3, 4, 3, 4, 3],
    [3, -4, -4, 3, -4, 3, 4, 4, 3, 4], [-4, 3, -4, -4, -4, -2, 1, -2, 1, 2, 1, 2], [5, 7, 8, 6],
    [5, 8, 6, 8, 5], [8, 10, 9, 10], [-11, -9, 10, -9, 5, 6, 8, 6, -2, 1, 2, 2, 1, 2],
    [-11, 12, 11], [-11, -11, -9, -9, 8, -9, 5, 7, 12, 6], [-11, 14, 11]]

end CFSG.Sporadic.Schreier

end
