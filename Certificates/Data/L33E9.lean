module

public import Mathlib
public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.L33TablesInputs

public section

namespace CFSG.Quasithin.E217L33

@[expose] def ea : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 1, 2] * List.formPerm [6, 8, 7] * List.formPerm [9, 11, 10] *
    List.formPerm [14, 23, 18] * List.formPerm [15, 17, 24] * List.formPerm [20, 25, 21]

@[expose] def eb : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 7, 11] * List.formPerm [1, 6, 10] * List.formPerm [2, 8, 9] *
    List.formPerm [13, 22, 16] * List.formPerm [15, 17, 24] * List.formPerm [20, 21, 25]

@[expose] def nine (a b : Equiv.Perm (Fin 26)) : List (Equiv.Perm (Fin 26)) :=
  [1, a, a ^ 2, b, a * b, a ^ 2 * b, b ^ 2, a * b ^ 2, a ^ 2 * b ^ 2]

@[expose] def stabList (L : List (Equiv.Perm (Fin 26))) (t f : Equiv.Perm (Fin 26)) :
    List (Equiv.Perm (Fin 26)) :=
  L.filter fun c => decide (c * t = t * c) &&
    (decide (c * f * c⁻¹ = f) || decide (c * f * c⁻¹ = f ^ 2))

@[expose] def e9Check (L : List (Equiv.Perm (Fin 26))) (t a b : Equiv.Perm (Fin 26)) : Bool :=
  decide (t ∈ L) && decide (t * t = 1) && decide (t ≠ 1) && decide (nine a b).Nodup &&
    (nine a b).all (fun x => decide (x ∈ L) && decide (t * x * t⁻¹ = x⁻¹) &&
      decide (x⁻¹ ∈ nine a b) && (nine a b).all fun y => decide (x * y ∈ nine a b)) &&
    L.all (fun c => !decide (c * t = t * c) ||
      (nine a b).all fun x => decide (c * x * c⁻¹ ∈ nine a b)) &&
    (nine a b).all fun f => decide (f = 1) || decide ((stabList L t f).length ≤ 12)

end CFSG.Quasithin.E217L33
