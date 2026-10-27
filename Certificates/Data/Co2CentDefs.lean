module

public import Certificates.Data.Co2Cent

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Monster.B.Co2 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271.Co2Cent

@[expose] noncomputable def co2XA : Equiv.Perm (Fin 2300) := permOfArr 2300 (dElts ())[3]!

@[expose] noncomputable def co2XB : Equiv.Perm (Fin 2300) := permOfArr 2300 (dElts ())[1]!

@[expose] noncomputable def uvGen (i : Fin 2) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (co2LGens ())[i.val]!

@[expose] noncomputable def Lsub : Subgroup (Equiv.Perm (Fin 2300)) :=
  closure (Set.range uvGen)

end CFSG.HardMathSupport.Dickson.I271

end
