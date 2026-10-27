module

public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

@[expose] def Bsub : Subgroup (Equiv.Perm (Fin 28)) :=
  QP.originalSubgroup ⊓ MulAction.stabilizer (Equiv.Perm (Fin 28)) (0 : Fin 28)

@[expose] def Bl : List (Equiv.Perm (Fin 28)) := (elemsT QP).filter fun g => decide (g 0 = 0)

@[expose] def Pl : List (Equiv.Perm (Fin 28)) := Bl.filter fun g => decide (g ^ 3 = 1)

end CFSG.SignalizerFunctorTheorem.NonLocalExc
