module

public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

@[expose] public section

namespace CFSG.Monster.GMS.S365

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs

@[expose] def eightCheck : Bool :=
  let O := orbitOf 2 98280
  let pos := posTable 24 O.pts
  let L := tyLab O.pts pos 98280
  L 2 == 3 && L 4 == 3 && L 6 == 3 &&
  L 1 == 1 && L (1 ^^^ 2) == 3 && L (1 ^^^ 4) == 3 && L (1 ^^^ 2 ^^^ 4) == 3 &&
  L 28 == 3 && L (28 ^^^ 2) == 1 && L (28 ^^^ 4) == 1 && L (28 ^^^ 2 ^^^ 4) == 1 &&
  L 40 == 1 && L (40 ^^^ 2) == 1 && L (40 ^^^ 4) == 1 && L (40 ^^^ 2 ^^^ 4) == 1

end CFSG.Monster.GMS.S365
