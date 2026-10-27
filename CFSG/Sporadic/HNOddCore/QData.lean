module

public import Init

public section

namespace CFSG.Sporadic.HNOddCore.QData

@[expose] def qFlat : Array (List Int) :=
  #[[-7, 9, -8, 7, 7, -7, 9], [-8, 7, 7, -7, 9, -8, 7, 7, -7, 9], [2, -8, 7, 7], [2, 4, 5, 4, 5, 6,
    5, 1, -10, -7, 4, 10, 4, 2, 2, 11, 2, 4, 5, 4, 5, 6, 5, 1, -10, -7, 4, 10, 4, 2, 11, 2, -7, 9,
    -7, 9, -8, 7, 7, -7, 9, -10, 1, 10, -7, 9], [1], [2, 4, 5, 4, 5, 6, 5, 1, -10, -7, 4, 10, 4, 1,
    2, 4, 5, 4, 5, 6, 5, 1, -10, -7, 4, 10, 4, 2, 2, 4, 5, 4, 5, 6, 5, 1, -10, -7, 4, 10, 4, -8, 7,
    7, -7, 9, -8, 7, 7, -7, 9], [-7, 9, -8, 7, 7, -7, 9, -7, 9, -8, 7, 7, -7, 9, -10, 1, 10], [1, 2,
    -7, 9, -8, 7, 7, -7, 9, 2, -7, 9, -7, 9, -8, 7, 7, -7, 9, -10, 1, 10, -7, 9, -7, 9, -8, 7, 7,
    -7, 9, -10, 1, 10]]

@[expose] def cvWords : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [], [1], [2], [-2, 10], [-7, 9], [-8, -7], [-14, 15, 14],
    [-4, 5, 4], [-5, 6, 5]]

@[expose] def cvBase : List (Fin 800) := [0, 1, 2, 3, 4]

@[expose] def cvSizes : List Nat := [1, 36, 16, 4, 2]

@[expose] def qWords : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [1], [2], [5], [-2, 6], [-2, -1, 3]]

@[expose] def qBase : List (Fin 800) := [0, 4, 3, 1, 2]

@[expose] def qSizes : List Nat := [4, 4, 2, 4, 2]

@[expose] def conjWords : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [], [], [4], [-7, 9], [11], [-4, 5, 4], [-5, -8, 10, 7],
    [-5, 10, 16, 7], [-11, -17], [-4, -10, -17, 4]]

@[expose] def conjBase : List (Fin 256) := [0, 4, 1, 8, 16]

@[expose] def conjSizes : List Nat := [1, 75, 16, 3, 4]

@[expose] def pbarWords : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [], [], [], [], [], [], [1], [2], [5], [-2, 6], [-2, -1, 3]]

@[expose] def pbarBase : List (Fin 800) := [0, 4, 3, 1, 2]

@[expose] def pbarSizes : List Nat := [256, 4, 2, 4, 2]

end CFSG.Sporadic.HNOddCore.QData
