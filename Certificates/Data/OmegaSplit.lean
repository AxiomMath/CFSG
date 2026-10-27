module

public import Certificates.Data.OmegaB0
public import Certificates.Data.OmegaF1051

public section

namespace Certificates.OmegaSplit

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def b0Elems (_ : Unit := ()) : List P45 :=
  Certificates.OmegaB0.bElems (Certificates.OmegaB0.phiTable (Certificates.OmegaB0.bl ()))
    (Certificates.OmegaB0.allVecs ())

end Certificates.OmegaSplit
