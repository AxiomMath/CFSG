module

public import CFSG.Sporadic.SuzRecog.LevelTwoComplex

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.RootTwist

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.Model

@[expose] def aPrime : Equiv.Perm (Fin 1782) := LevelTwo.aP LevelTwo.p1

@[expose] def CW : Subgroup (Equiv.Perm (Fin 1782)) :=
  centralizer ({suzInv 1, aPrime} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM

end CFSG.Sporadic.SuzRecog.RootTwist
