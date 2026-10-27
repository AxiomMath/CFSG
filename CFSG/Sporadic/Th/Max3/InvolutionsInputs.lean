
module


public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.InvRep

open CFSG.Sporadic.Th.Native

@[expose] def dWord : List Gen :=
  [.y, .y, .y, .y, .x, .y, .y, .y, .x, .y, .x, .y, .y, .y, .y, .x, .y, .x, .y, .y, .x, .y, .x, .y,
    .y, .y, .y]

@[expose] def rowsD : Array V4 := wordRows rowsX rowsY dWord

@[expose] def rowsXNf (k : Fin 512) : Array V4 := mulRows rowsX (rowsNfAt k)

@[expose] def rowsDNf (k : Fin 512) : Array V4 := mulRows rowsD (rowsNfAt k)

end CFSG.Sporadic.Th.Max3.InvRep
