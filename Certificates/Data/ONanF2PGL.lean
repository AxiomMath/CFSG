module

public import CFSG.GH74.KGroups.L34Inputs
public import CFSG.GH74.KGroups.L34AutInputs
public import CFSG.GH74.KGroups.PermCheck

public section

namespace CFSG.OddStandard.ONanRec.F2

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates CFSG.Sporadic.Schreier

@[expose] def pElems : List (Equiv.Perm (Fin 42)) := elemsT QP

@[expose] def cosetReps : List (Equiv.Perm (Fin 42)) :=
  [1, sg0, sg1, sg2,
    List.formPerm [0, 28, 9, 23] * List.formPerm [1, 31, 15, 22] * List.formPerm [2, 38, 8, 21] * List.formPerm [3, 37, 18, 24] * List.formPerm [4, 25] * List.formPerm [5, 26, 16, 32] * List.formPerm [6, 29] * List.formPerm [7, 27, 19, 35] * List.formPerm [10, 34, 12, 33] * List.formPerm [11, 39] * List.formPerm [13, 36] * List.formPerm [14, 40, 17, 41] * List.formPerm [20, 30],
    List.formPerm [0, 14, 5, 13, 4, 17, 20, 7] * List.formPerm [1, 11, 10, 18, 3, 8, 15, 12] * List.formPerm [6, 16, 19, 9] * List.formPerm [21, 39, 37, 34, 33, 22, 38, 24] * List.formPerm [23, 41, 26, 36] * List.formPerm [25, 40, 32, 35, 28, 29, 30, 27],
    List.formPerm [0, 36, 13, 32, 20, 35, 1, 31, 7, 25] * List.formPerm [2, 41, 18, 34, 17, 21, 9, 33, 3, 26] * List.formPerm [4, 23, 12, 27, 19, 37, 5, 30, 14, 40] * List.formPerm [6, 29, 16, 22, 11, 38, 8, 39, 15, 28] * List.formPerm [10, 24],
    List.formPerm [0, 19, 7, 20, 1, 14, 16, 6] * List.formPerm [2, 5, 17, 11, 3, 12, 10, 13] * List.formPerm [8, 18, 15, 9] * List.formPerm [21, 36, 25, 35, 30, 40, 41, 23] * List.formPerm [22, 34, 29, 33, 28, 27, 38, 31] * List.formPerm [24, 37, 39, 26],
    List.formPerm [0, 39, 10, 34, 13, 27, 17, 38, 6, 37] * List.formPerm [1, 36, 15, 31, 7, 26, 11, 23, 19, 41] * List.formPerm [2, 29] * List.formPerm [3, 25, 5, 24, 12, 28, 8, 32, 9, 33] * List.formPerm [4, 30, 20, 40, 18, 21, 14, 35, 16, 22],
    List.formPerm [0, 1, 10] * List.formPerm [2, 14, 9] * List.formPerm [3, 6, 11] * List.formPerm [4, 18, 12] * List.formPerm [5, 15, 13] * List.formPerm [7, 19, 8] * List.formPerm [16, 17, 20] * List.formPerm [21, 23, 38] * List.formPerm [22, 29, 40] * List.formPerm [24, 32, 41] * List.formPerm [25, 35, 39] * List.formPerm [26, 27, 30] * List.formPerm [28, 37, 34] * List.formPerm [31, 36, 33],
    List.formPerm [0, 17, 4, 13, 2, 5] * List.formPerm [3, 9] * List.formPerm [6, 18, 10] * List.formPerm [7, 20] * List.formPerm [8, 19, 16, 11, 12, 15] * List.formPerm [21, 26] * List.formPerm [22, 34, 37, 39, 41, 23] * List.formPerm [24, 38, 36] * List.formPerm [25, 30, 35, 32, 40, 31] * List.formPerm [28, 29],
    List.formPerm [0, 27, 12, 38, 1, 35] * List.formPerm [2, 39, 9, 36, 20, 32] * List.formPerm [3, 22, 10, 24, 16, 29] * List.formPerm [4, 31, 11, 33, 8, 23] * List.formPerm [5, 37, 19, 25, 7, 40] * List.formPerm [6, 30, 14, 28, 15, 26] * List.formPerm [13, 21, 17, 34, 18, 41]]

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
