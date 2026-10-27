module

public import Mathlib

public section

namespace CFSG.Quasithin.E217B1L27

@[expose] def gS : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 1, 2, 7] * List.formPerm [3, 5, 4, 6]

@[expose] def hS : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 4] * List.formPerm [5, 7]

@[expose] def z0 : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 2] * List.formPerm [1, 7] * List.formPerm [3, 4] * List.formPerm [5, 6]

@[expose] def closureList (gens : List (Equiv.Perm (Fin 8))) :
    ℕ → List (Equiv.Perm (Fin 8))
  | 0 => [1]
  | n + 1 => ((closureList gens n) ++
      gens.flatMap fun g => (closureList gens n).map fun x => g * x).eraseDups

@[expose] def sList : List (Equiv.Perm (Fin 8)) := closureList [gS, hS] 6

@[expose] def l27Check (LP : List (Equiv.Perm (Fin 8))) : Bool :=
  decide sList.Nodup && decide (sList.length = 8) &&
    sList.all (fun x => decide (x ∈ LP) && decide (x⁻¹ ∈ sList) &&
      sList.all fun y => decide (x * y ∈ sList)) &&
    decide (z0 ∈ sList) && decide (z0 * z0 = 1) && decide (z0 ≠ 1) &&
    sList.all (fun s => decide (z0 * s = s * z0)) &&
    LP.all (fun g => !decide (g * z0 = z0 * g) || decide (g ∈ sList)) &&
    LP.all (fun g => !(sList.all fun s => decide (g * s * g⁻¹ ∈ sList)) || decide (g ∈ sList))

end CFSG.Quasithin.E217B1L27
