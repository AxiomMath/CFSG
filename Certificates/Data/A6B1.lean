module

public import Mathlib

public section

namespace CFSG.Quasithin.E217A6

@[expose] def gS : Equiv.Perm (Fin 10) :=
  List.formPerm [2, 5, 9, 8] * List.formPerm [3, 7, 4, 6]

@[expose] def hS : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 1] * List.formPerm [3, 7] * List.formPerm [4, 6] * List.formPerm [5, 8]

@[expose] def gP : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 5, 1, 8] * List.formPerm [3, 4, 7, 6]

@[expose] def z0 : Equiv.Perm (Fin 10) :=
  List.formPerm [2, 9] * List.formPerm [3, 4] * List.formPerm [5, 8] * List.formPerm [6, 7]

@[expose] def closureList (gens : List (Equiv.Perm (Fin 10))) :
    ℕ → List (Equiv.Perm (Fin 10))
  | 0 => [1]
  | n + 1 => ((closureList gens n) ++
      gens.flatMap fun g => (closureList gens n).map fun x => g * x).eraseDups

@[expose] def sList : List (Equiv.Perm (Fin 10)) := closureList [gS, hS] 6

@[expose] def p1List : List (Equiv.Perm (Fin 10)) := closureList [gS, hS, gP] 6

@[expose] def a6Check (LP LA : List (Equiv.Perm (Fin 10))) : Bool :=
  decide sList.Nodup && decide (sList.length = 8) &&
    sList.all (fun x => decide (x ∈ LP) && decide (x⁻¹ ∈ sList) &&
      sList.all fun y => decide (x * y ∈ sList)) &&
    LP.all (fun g => !(sList.all fun s => decide (g * s * g⁻¹ ∈ sList)) || decide (g ∈ sList)) &&
    decide (z0 ∈ sList) && decide (z0 * z0 = 1) &&
    decide p1List.Nodup && decide (p1List.length = 24) &&
    p1List.all (fun x => decide (x ∈ LP) && decide (x⁻¹ ∈ p1List) &&
      p1List.all fun y => decide (x * y ∈ p1List)) &&
    sList.all (fun s => decide (s ∈ p1List)) &&
    LP.all (fun x => decide (x ∈ LA)) &&
    LA.all (fun a => !(decide (a * a = 1) && sList.all fun s => decide (a * s = s * a)) ||
      decide (a = 1) || decide (a = z0) ||
      LA.all fun b => !(sList.all fun s => decide (b * s * b⁻¹ ∈ sList)) ||
        decide (a * b ≠ b * a) || p1List.all fun p => decide (b * p * b⁻¹ ∈ p1List)) &&
    LP.all (fun u => !(decide (u * u = 1) && decide (u ≠ 1)) ||
      LP.any fun g => decide ((u * (g * u * g⁻¹)) ^ 5 = 1) &&
        decide ((u * (g * u * g⁻¹)) ^ 3 ≠ 1))

end CFSG.Quasithin.E217A6
