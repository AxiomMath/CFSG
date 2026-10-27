module

public import CFSG.Quasithin.Background.HSporLatInputs

public section

namespace CFSG.Quasithin.H.MathieuLat

@[expose] def m23Incl : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1], [2], [1, 3, 5], [4, 5], [5],
    [5, 6], [1, 2, 7, 8], [8], [2, 5, 9], [1, 2, 3, 5, 7, 8, 9, 10, 15], [1, 3, 4, 5, 6, 11],
    [4, 5, 8, 12, 15], [5, 8, 13, 15], [5, 6, 8, 14, 15], [5, 8, 15]]

end CFSG.Quasithin.H.MathieuLat
