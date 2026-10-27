module

public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

@[expose] public section

namespace CFSG.Monster.GMS.ASegConn

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

@[expose] def diamCheckT (O : VOrbit) : Bool :=
  let pos := posTable 24 O.pts
  let inO := inPts O.pts pos 98280
  let nbr : List ℕ := ((List.range 98280).filter fun q => inO (O.pts[0]! ^^^ O.pts[q]!)).map
    fun q => O.pts[q]!
  (List.range 98280).all fun p => inO (O.pts[0]! ^^^ O.pts[p]!) ||
    nbr.any fun w => inO (O.pts[p]! ^^^ w)

@[expose] def diamCheck : Bool := diamCheckT (orbitOf 2 98280)

end CFSG.Monster.GMS.ASegConn
