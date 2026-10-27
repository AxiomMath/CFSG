module

public import CFSG.Monster.GMS.S365Facts
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

@[expose] public section

namespace CFSG.Monster.Tri

open CFSG.Monster.GMS CFSG.Monster.GMS.S365 CFSG.Sporadic.Co1.Module.Pairs
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (orbitOf)

@[expose] def wData : List (ℕ × ℕ) := [(154, 40), (290, 42), (894, 44), (10, 46)]

@[expose] def wCheck : Bool :=
  let O := orbitOf 2 98280
  let pos := posTable 24 O.pts
  wData.all fun pω =>
    tyLab O.pts pos 98280 pω.1 == 3 && tyLab O.pts pos 98280 (pω.1 ^^^ 2) == 3 &&
      tyLab O.pts pos 98280 (pω.1 ^^^ 4) == 3 && tyLab O.pts pos 98280 (pω.1 ^^^ pω.2) == 3

@[expose] def baseCheck : Bool :=
  let O := orbitOf 2 98280
  let pos := posTable 24 O.pts
  tyLab O.pts pos 98280 2 == 3 && tyLab O.pts pos 98280 4 == 3 &&
    tyLab O.pts pos 98280 (2 ^^^ 4) == 3 && tyLab O.pts pos 98280 40 == 1 &&
      tyLab O.pts pos 98280 (40 ^^^ 2) == 1 && tyLab O.pts pos 98280 (40 ^^^ 4) == 1 &&
        tyLab O.pts pos 98280 (40 ^^^ 2 ^^^ 4) == 1

end CFSG.Monster.Tri
