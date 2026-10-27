
module


public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.AltQuot

open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

@[expose] def carmWord : Fin 9 → List Gen :=
  ![[], [],
    [.y, .x, .y, .x, .y, .x, .y, .y, .x, .y, .x, .y,
      .y, .x, .y, .x, .y, .y, .y, .y, .y, .x, .y],
    [.x, .y, .y, .y, .y, .y, .x, .y, .y, .x, .y, .x,
      .y, .x, .y, .y, .x, .y, .x, .y, .y, .x, .y],
    [.y, .x, .y, .y, .y, .y, .x, .y, .x, .y, .y, .y,
      .x, .y, .x, .y, .x, .y, .y, .y, .y, .x, .y, .x],
    [.y, .y, .x, .y, .x, .y, .y, .y, .y, .x, .y, .y,
      .x, .y, .x, .y, .y, .y, .y, .x, .y, .y, .y, .y],
    [.y, .y, .x, .y, .y, .y, .y, .x, .y, .x, .y, .y,
      .y, .y, .y, .x, .y, .y, .x, .y],
    [.x, .y, .x, .y, .x, .y, .y, .y, .x, .y, .y, .y,
      .x, .y, .y, .y, .y, .x, .y, .y, .x, .y],
    [.x, .y, .y, .x, .y, .x, .y, .x, .y, .y, .x, .y,
      .x, .y, .y, .x, .y, .x, .y, .y, .y, .y, .y]]

@[expose] def carmRows (k : CarmichaelIndex 9) : Array V4 := wordRows rowsX rowsY (carmWord k.1)

@[expose] def waRows : Array V4 :=
  mulRows (mulRows (mulRows (mulRows (mulRows (mulRows (mulRows (mulRows
    (carmRows (carmIdx 2)) (powRows (carmRows (carmIdx 3)) 2)) (carmRows (carmIdx 2)))
    (carmRows (carmIdx 4))) (powRows (carmRows (carmIdx 5)) 2)) (carmRows (carmIdx 4)))
    (carmRows (carmIdx 6))) (powRows (carmRows (carmIdx 7)) 2)) (carmRows (carmIdx 6))

@[expose] def wbRows : Array V4 :=
  mulRows (mulRows (mulRows (mulRows (mulRows (mulRows (mulRows
    (powRows (carmRows (carmIdx 2)) 2) (carmRows (carmIdx 3)))
    (powRows (carmRows (carmIdx 4)) 2)) (carmRows (carmIdx 3)))
    (powRows (carmRows (carmIdx 5)) 2)) (carmRows (carmIdx 6)))
    (powRows (carmRows (carmIdx 7)) 2)) (carmRows (carmIdx 8))

@[expose] def rowsNfIdx (k : Fin 512) : Array V4 :=
  rowsNf (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2

@[expose] def rowsCommXQ :
    Array V4 := mulRows (mulRows (mulRows rowsX (rowsQ 1)) rowsX) (rowsQ 1)

end CFSG.Sporadic.Th.Max3.AltQuot
