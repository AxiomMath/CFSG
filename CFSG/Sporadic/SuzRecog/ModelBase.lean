module

public import CFSG.Sporadic.SuzOddCore.InvPerms
public import Certificates.Data.SuzLevelTwoBase

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.Model

open CFSG.Sporadic.SuzOddCore

@[expose] def rho1 : Equiv.Perm (Fin 1782) := permC 1782 LevelTwoData.rhoArr

@[expose] def w0 : Equiv.Perm (Fin 1782) := permC 1782 LevelTwoData.w0Arr

@[expose] def R0 : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure {w0, rho1 * w0 * rho1⁻¹}

@[expose] def NR0 : Subgroup (Equiv.Perm (Fin 1782)) :=
  suzM ⊓ Subgroup.normalizer (R0 : Set (Equiv.Perm (Fin 1782)))

@[expose] def B0 : Subgroup (Equiv.Perm (Fin 1782)) :=
  invE 1 ⊓ Subgroup.normalizer (R0 : Set (Equiv.Perm (Fin 1782)))

@[expose] def Crho1 : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.centralizer {rho1} ⊓ suzM

end CFSG.Sporadic.SuzRecog.Model
