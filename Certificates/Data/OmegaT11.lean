module

public import Certificates.Data.OmegaInv

public section

namespace Certificates.OmegaT11

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier
open Certificates.OmegaInv

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def zeta0 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 9] * List.formPerm [4, 10] * List.formPerm [5, 11] *
    List.formPerm [6, 12] * List.formPerm [7, 13] * List.formPerm [8, 14] *
    List.formPerm [25, 35] * List.formPerm [26, 44] * List.formPerm [27, 42] *
    List.formPerm [28, 43] * List.formPerm [29, 38] * List.formPerm [30, 36] *
    List.formPerm [31, 37] * List.formPerm [32, 41] * List.formPerm [33, 39] *
    List.formPerm [34, 40])

@[expose] def g1 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 1, 2] * List.formPerm [3, 5, 4] * List.formPerm [6, 7, 8] *
    List.formPerm [9, 11, 10] * List.formPerm [12, 13, 14] * List.formPerm [16, 21, 23] *
    List.formPerm [17, 19, 24] * List.formPerm [18, 20, 22] * List.formPerm [26, 31, 33] *
    List.formPerm [27, 29, 34] * List.formPerm [28, 30, 32] * List.formPerm [36, 41, 43] *
    List.formPerm [37, 39, 44] * List.formPerm [38, 40, 42])

@[expose] def g2 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 2, 21] * List.formPerm [1, 16, 23] * List.formPerm [3, 8, 32] *
    List.formPerm [4, 37, 6] * List.formPerm [5, 30, 39] * List.formPerm [7, 44, 28] *
    List.formPerm [9, 14, 41] * List.formPerm [10, 31, 12] * List.formPerm [11, 36, 33] *
    List.formPerm [13, 26, 43] * List.formPerm [17, 20, 18] * List.formPerm [19, 22, 24] *
    List.formPerm [25, 38, 40] * List.formPerm [29, 34, 35])

@[expose] def lam0 (_ : Unit := ()) : P45 := Certificates.OmegaT0.yB ()

@[expose] def centL (A0 : List P45) (a : P45) : List P45 :=
  A0.filter fun g => decide (g * a = a * g)

@[expose] def cubeL (C : List P45) : List P45 :=
  C.filter fun g => decide (g ^ 3 = 1 ∧ g ≠ 1)

@[expose] def k1Chk (A0 P0 C C3 : List P45) (a z : P45) : Bool :=
  decide (z ∈ P0) && decide (z * z = 1 ∧ z ≠ 1) && decide (cntL A0 z = 1152) &&
    decide (z * a = a * z) && C3.all (fun g => decide (g * z = z * g)) &&
    C.all fun g => decide (g ^ 96 = 1)

@[expose] def k2Chk (P0 C3 : List P45) (a z l b1 b2 : P45) : Bool :=
  decide (l ∈ P0) && decide (b1 ∈ P0) && decide (b2 ∈ P0) && decide (b1 ∈ C3) &&
    decide (b2 ∈ C3) && decide (b1 * b2 * (b1 * b2) = 1 ∧ b1 * b2 ≠ 1) &&
    decide (a⁻¹ * l⁻¹ * a * l = b1 * b2 * z)

@[expose] def k3Chk (A0 P0 C C3 : List P45) (z : P45) : Bool :=
  C.all fun x => !(C3.all (fun g => decide (g * x = x * g)) && decide (x * x = 1 ∧ x ≠ 1) &&
    decide (x ∈ P0) && decide (cntL A0 x = 1152)) || decide (x = z)

@[expose] def k4Chk (A0 C3 : List P45) (z : P45) : Bool :=
  C3.all fun a1 => C3.all fun a2 => !decide (a1 * a2 * (a1 * a2) = 1 ∧ a1 * a2 ≠ 1) ||
    (decide (a1 * a2 * z * (a1 * a2 * z) = 1 ∧ a1 * a2 * z ≠ 1) &&
      decide (cntL A0 (a1 * a2 * z) = 192))

@[expose] def check (_ : Unit := ()) : Bool :=
  let A0 := elemsT QA45
  let P0 := elemsT QP45
  let a := r3 ()
  let z := zeta0 ()
  let C := centL A0 a
  let C3 := cubeL C
  k1Chk A0 P0 C C3 a z && k2Chk P0 C3 a z (lam0 ()) (g1 ()) (g2 ()) && k3Chk A0 P0 C C3 z &&
    k4Chk A0 C3 z

end Certificates.OmegaT11
