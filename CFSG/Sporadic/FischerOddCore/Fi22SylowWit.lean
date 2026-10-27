module

public import CFSG.Sporadic.FischerOddCore.Fi22Cent

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

@[expose] def fi22SylX (s w : ℕ) : Equiv.Perm (Fin 3510) :=
  fi22CentWitRep (fi22CentSylowField s 6 + w)

@[expose] def fi22SylH (s w : ℕ) : Equiv.Perm (Fin 3510) :=
  fi22CentWitConj (fi22CentSylowField s 6 + w)

end CFSG.Sporadic.FischerOddCore
