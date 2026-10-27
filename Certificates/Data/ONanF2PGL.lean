module

public import CFSG.GH74.KGroups.L34Inputs
public import CFSG.GH74.KGroups.L34AutInputs
public import CFSG.GH74.KGroups.PermCheck

public section

namespace CFSG.OddStandard.ONanRec.F2

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates CFSG.Sporadic.Schreier

@[expose] def pElems : List (Equiv.Perm (Fin 42)) := elemsT QP

def genA : List (Equiv.Perm (Fin 42)) := [PA, PB, sg0, sg1, sg2]

def insertRep (reps : List (Equiv.Perm (Fin 42))) (c : Equiv.Perm (Fin 42)) :
    List (Equiv.Perm (Fin 42)) :=
  if reps.all (fun r => !QP.sift (r⁻¹ * c) 0) then reps ++ [c] else reps

def repsRound (reps : List (Equiv.Perm (Fin 42))) : List (Equiv.Perm (Fin 42)) :=
  (genA.flatMap fun g => reps.map fun r => tab (g * r)).foldl insertRep reps

def cosetReps : List (Equiv.Perm (Fin 42)) := (repsRound^[12]) [tab 1]

def rep (i : Fin 12) : Equiv.Perm (Fin 42) := cosetReps.getD i 1

@[expose] def factPglCount : Prop :=
  (pElems.filter (fun g => decide (orderIs g 4 = true))).length = 3780

@[expose] def factPglCent : Prop :=
  (pElems.filter (fun g => decide (g * PB = PB * g))).length = 16

@[expose] def factPglCosets : Prop :=
  (∀ i : Fin 12, QA.sift (rep i) 0 = true) ∧
  (∀ i j : Fin 12, i ≠ j → QP.sift ((rep i)⁻¹ * rep j) 0 = false) ∧
  (∀ i : Fin 12, QP.sift (rep i) 0 = true ∨ QP.sift (rep i ^ 3) 0 = false ∨
    pElems.all (fun p => decide (rep i * p * PB ≠ PB * (rep i * p))) = true)

instance : Decidable factPglCount := by
  unfold factPglCount
  infer_instance

instance : Decidable factPglCent := by
  unfold factPglCent
  infer_instance

instance : Decidable factPglCosets := by
  unfold factPglCosets
  infer_instance

@[expose] def pglCheck : Bool :=
  decide factPglCount && decide factPglCent && decide factPglCosets

end CFSG.OddStandard.ONanRec.F2
