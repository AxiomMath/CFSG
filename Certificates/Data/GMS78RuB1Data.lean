module

public section

namespace CFSG.Sporadic.RuSchreier.RuB1

@[expose] def e8ConjWords : List (List Int) :=
  [[], [1], [2], [3], [4], [-4], [2, 1], [3, 1], [4, 1], [3, 2], [4, 2], [1, 3], [4, 3], [1, 4],
    [2, 4], [3, 4], [4, 4], [3, -4], [-4, -4], [-4, 1], [2, -4], [-4, 2], [1, -4], [-4, 3]]

@[expose] def e8BigIdx : List Nat := [29, 24, 25, 8, 17, 18, 12, 33]

end CFSG.Sporadic.RuSchreier.RuB1
