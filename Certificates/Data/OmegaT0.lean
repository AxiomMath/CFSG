module

public import Certificates.Data.PSp43Sylow

public section

namespace Certificates.OmegaT0

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def z0 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [4, 7] * List.formPerm [5, 8] *
    List.formPerm [9, 12] * List.formPerm [10, 13] * List.formPerm [11, 14] *
    List.formPerm [17, 19] * List.formPerm [18, 22] * List.formPerm [21, 23] *
    List.formPerm [27, 29] * List.formPerm [28, 32] * List.formPerm [31, 33] *
    List.formPerm [37, 39] * List.formPerm [38, 42] * List.formPerm [41, 43])

@[expose] def yB (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 17] * List.formPerm [2, 19] * List.formPerm [3, 29] *
    List.formPerm [4, 37] * List.formPerm [5, 14] * List.formPerm [6, 27] * List.formPerm [7, 39] *
    List.formPerm [8, 11] * List.formPerm [9, 38] * List.formPerm [10, 31] *
    List.formPerm [12, 42] * List.formPerm [13, 33] * List.formPerm [18, 23] *
    List.formPerm [21, 22] * List.formPerm [25, 30] * List.formPerm [26, 34] *
    List.formPerm [28, 41] * List.formPerm [32, 43] * List.formPerm [35, 36] *
    List.formPerm [40, 44])

@[expose] def za (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 3, 2, 6] * List.formPerm [4, 8, 7, 5] * List.formPerm [9, 21, 12, 23] *
    List.formPerm [10, 32, 13, 28] * List.formPerm [11, 37, 14, 39] * List.formPerm [15, 16] *
    List.formPerm [17, 27, 19, 29] * List.formPerm [18, 42, 22, 38] * List.formPerm [20, 24] *
    List.formPerm [25, 30] * List.formPerm [26, 34] * List.formPerm [31, 41, 33, 43] *
    List.formPerm [35, 44] * List.formPerm [36, 40])

@[expose] def zb (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 4, 2, 7] * List.formPerm [3, 5, 6, 8] * List.formPerm [9, 41, 12, 43] *
    List.formPerm [10, 22, 13, 18] * List.formPerm [11, 27, 14, 29] * List.formPerm [15, 20] *
    List.formPerm [16, 24] * List.formPerm [17, 39, 19, 37] * List.formPerm [21, 31, 23, 33] *
    List.formPerm [25, 34] * List.formPerm [26, 30] * List.formPerm [28, 38, 32, 42] *
    List.formPerm [35, 36] * List.formPerm [40, 44])

@[expose] def ya (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 5, 2, 8] * List.formPerm [3, 7, 6, 4] * List.formPerm [9, 31, 12, 33] *
    List.formPerm [10, 42, 13, 38] * List.formPerm [11, 17, 14, 19] * List.formPerm [15, 24] *
    List.formPerm [16, 20] * List.formPerm [18, 28, 22, 32] * List.formPerm [21, 43, 23, 41] *
    List.formPerm [25, 26] * List.formPerm [27, 37, 29, 39] * List.formPerm [30, 34] *
    List.formPerm [35, 40] * List.formPerm [36, 44])

@[expose] def yb (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 18] * List.formPerm [2, 22] * List.formPerm [3, 29] *
    List.formPerm [5, 41] * List.formPerm [6, 27] * List.formPerm [8, 43] * List.formPerm [9, 38] *
    List.formPerm [11, 32] * List.formPerm [12, 42] * List.formPerm [14, 28] *
    List.formPerm [17, 23] * List.formPerm [19, 21] * List.formPerm [25, 44] *
    List.formPerm [26, 35] * List.formPerm [30, 40] * List.formPerm [34, 36])


@[expose] def sylowChk (_ : Unit := ()) : Bool :=
  let T := elemsT QT0
  decide ((T.filter fun g => T.all fun t => decide (g * t = t * g)).length = 2) &&
    (elemsT QA45).all fun a => !(T.all fun t => decide (a * t = t * a)) || decide (a ∈ T)

@[expose] def coverOK (reps L : List P45) : Bool :=
  L.all fun t => !decide (t * t = 1 ∧ t ≠ 1) ||
    L.any fun g => reps.any fun r => decide (g * t * g⁻¹ = r)

@[expose] def cntCent (L : List P45) (r : P45) : ℕ :=
  (L.filter fun g => decide (g * r = r * g)).length

@[expose] def n7Chk (_ : Unit := ()) : Bool :=
  let L0 := elemsT QP45
  let T := elemsT QT0
  let z := z0 ()
  let y := yB ()
  let a := za ()
  let b := zb ()
  let c := ya ()
  let d := yb ()
  coverOK [z, y] L0 && decide (z ∈ T) && decide (y ∈ T) &&
    decide (cntCent L0 z = 576) && decide (cntCent T z = 64) &&
    decide (cntCent L0 y = 96) && decide (cntCent T y = 32) &&
    decide (a ∈ T) && decide (b ∈ T) && decide (a * z = z * a) && decide (b * z = z * b) &&
    decide (a * b * a⁻¹ * b⁻¹ = z) &&
    decide (c ∈ T) && decide (d ∈ T) && decide (c * y = y * c) && decide (d * y = y * d) &&
    decide (c * d * c⁻¹ * d⁻¹ = y)

@[expose] def check (_ : Unit := ()) : Bool := sylowChk () && n7Chk ()

end Certificates.OmegaT0
