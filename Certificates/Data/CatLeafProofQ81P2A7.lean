module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.A7Data

open Equiv

@[expose] def cubes : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun g => g ^ 3 = 1

@[expose] def cubeCent (π : Perm (Fin 7)) : Finset (Perm (Fin 7)) :=
  cubes.filter fun g => g * π = π * g

@[expose] def pairOK (S : Finset (Perm (Fin 7))) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, g ≠ 1 → g * h = h * g → h = 1 ∨ h = g ∨ h = g * g

instance (S : Finset (Perm (Fin 7))) : Decidable (pairOK S) := by
  unfold pairOK
  infer_instance

@[expose] def a7E9 : Prop :=
  ∀ π : Perm (Fin 7), π * π = 1 → π ≠ 1 → pairOK (cubeCent π)

instance : Decidable a7E9 := by
  unfold a7E9
  infer_instance

end CFSG.ComponentClassification.HarrisLit.L33.A7Data
