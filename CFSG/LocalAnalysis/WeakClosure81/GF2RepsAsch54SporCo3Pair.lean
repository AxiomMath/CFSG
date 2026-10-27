module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo3Inputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporCo3

open CFSG.Sporadic.Schreier.Co3
open CFSG.Monster.B.Co2 (permOfArr)

@[expose] def pairAS : Array (Array Nat) := co3TArrs.extract 0 8 ++ pairAArrs

@[expose] def pairBS : Array (Array Nat) := co3TArrs.extract 0 8 ++ pairBArrs

@[expose] def pairA : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure {g | ∃ i < 17, permOfArr 276 pairAS[i]! = g}

@[expose] def pairB : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure {g | ∃ i < 18, permOfArr 276 pairBS[i]! = g}

end CFSG.LocalAnalysis.WeakClosure81.SporCo3

end
