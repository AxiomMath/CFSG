module

public section

namespace CFSG.D4Hex

@[expose] def locStepWords : List (Bool × List Nat) :=
  [(true, [0]), (true, [1]), (true, [2]), (true, [6]), (true, [3, 2, 4, 2]),
    (false, [1, 4, 5, 2, 5, 6, 1, 6, 7]), (true, [0, 2, 6, 2, 6, 0, 3, 1, 2]),
    (true, [3, 0, 6, 0, 6, 3, 1, 5]), (false, [6, 7, 0, 6, 1, 6, 0, 3, 0, 6, 2, 6, 3, 2, 5]),
    (true, [6, 1, 2, 6, 2, 6, 0, 6, 0, 2, 4, 1, 2]), (true, [6, 1, 5, 1, 2]),
    (false, [6, 7, 0, 6, 0, 6, 5, 4, 1, 3, 1])]

@[expose] def locU0Word : List Nat := [0, 2, 6, 0, 2]

end CFSG.D4Hex
