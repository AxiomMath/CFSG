module

public import Init

public section

namespace CFSG.Sporadic.Schreier

@[expose] def m24Derivs : List (List Int) :=
  [[1, 2], [1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1], [-3, -4, -4, 3, 4, 3, 3], [-5, -4, -4, 5, 5, 5],
    [-6, -5, -5, 4, 5, 4, 4], [-6, -6, -6, 7, 6, 7, 6, 6], [7, 8, -6, -6, 7, -5, -4, -5, 4, 5, 5, 4],
    [-6, -9, 6, 6, 6], [-3, -4, -3, 4, 3, 4, 3], [-6, -6, 7, -9, -5, 11, 5], [7, -10, 12, 10],
    [-13, -9, -12, 7, 12]]

end CFSG.Sporadic.Schreier

end
