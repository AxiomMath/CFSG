module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs

@[expose] public section

open CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Schreier CFSG.Certificates
open scoped Pointwise

namespace Certificates

abbrev closureU (gs : List (Equiv.Perm (Fin 693))) : Subgroup (Equiv.Perm (Fin 693)) :=
  Subgroup.closure {g | g ∈ gs}


end Certificates
