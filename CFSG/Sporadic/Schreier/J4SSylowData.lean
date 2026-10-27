
module

public import CFSG.Sporadic.Schreier.J4SOrbitsBase

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

@[expose] def ell (a : ℕ) : ℕ := (List.range 11).foldl (fun s j => s ^^^ (if (a &&& 300).testBit j
  then 1 else 0)) 0

@[expose] def spanIdx : Array ℕ := normalOrbitSpanBasis.toArray.map fun b =>
  ((List.range 1024).find? fun e => app11 elementColumns[e]! 4 == b).getD 0

end CFSG.Sporadic.J4Schreier
