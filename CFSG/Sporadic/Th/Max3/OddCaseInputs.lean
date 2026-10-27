
module


public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.Sporadic.Th

open Native Max3

@[expose] def rowsEQ : Fin 4 → Array V4 :=
  ![rowsQ 0, mulRows (rowsQ 1) (rowsQ 2), mulRows (rowsQ 1) (rowsQ 5), rowsQ 7]

@[expose] def rowsFQ : Fin 4 → Array V4 :=
  ![mulRows (mulRows (rowsQ 1) (rowsQ 3)) (rowsQ 4), rowsQ 3, mulRows (rowsQ 3) (rowsQ 6),
    mulRows (rowsQ 3) (rowsQ 4)]

end CFSG.Sporadic.Th
