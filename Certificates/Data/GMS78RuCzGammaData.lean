module

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

@[expose] def c2ImgCodes : List (List Nat) :=
  [[6, 4, 1, 6, 2, 0], [2, 5, 6, 2, 6, 0], [8, 4, 4, 9, 4], [0, 2, 5, 6, 0, 0], [2, 0, 8, 2, 4, 0],
   [9, 0, 6, 4, 8, 10]]

@[expose] def c2InvCodes : List (List Nat) :=
  [[6, 4, 1, 6, 2, 0], [2, 5, 6, 2, 6, 0], [8, 4, 4, 9, 4], [0, 2, 5, 6, 0, 0], [2, 0, 8, 2, 4, 0],
   [8, 0, 6, 4, 9, 10]]

@[expose] def c2JCodes : List (List Nat) :=
  [[1], [2], [10, 4, 11], [4, 1, 6, 4, 0], [2, 6, 9, 6, 2], [11, 4, 2, 4, 2]]

@[expose] def c2TrivCodes : List (List Nat) :=
  [[0, 0], [], [6, 1, 6, 0], [9, 4, 8, 4], [4, 3, 0, 4, 2, 0], [8, 4, 8, 4], [], [4, 3, 4, 2, 0],
   [8, 6, 8, 6, 0]]

@[expose] def c2BCodes : List (List Nat) :=
  [[6, 4, 1, 6, 2, 0], [2, 5, 6, 2, 6, 0], [4, 2, 6, 4, 4, 6, 2], [0, 2, 5, 6, 0, 0]]

end CFSG.ComponentClassification.GMS78.RuCz
