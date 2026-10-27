module

public import Certificates.Data.OmegaT0
public import Certificates.Data.OmegaF1051

public section

namespace Certificates.OmegaInv

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def r3 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 6] * List.formPerm [4, 8] * List.formPerm [5, 7] *
    List.formPerm [9, 12] * List.formPerm [10, 14] * List.formPerm [11, 13] *
    List.formPerm [17, 22] * List.formPerm [18, 19] * List.formPerm [20, 24] *
    List.formPerm [25, 35] * List.formPerm [26, 36] * List.formPerm [27, 42] *
    List.formPerm [28, 39] * List.formPerm [29, 38] * List.formPerm [30, 44] *
    List.formPerm [31, 41] * List.formPerm [32, 37] * List.formPerm [33, 43] *
    List.formPerm [34, 40])

@[expose] def r4 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 12] * List.formPerm [4, 14] * List.formPerm [5, 13] *
    List.formPerm [6, 9] * List.formPerm [7, 11] * List.formPerm [8, 10] *
    List.formPerm [17, 22] * List.formPerm [18, 19] * List.formPerm [20, 24] *
    List.formPerm [26, 30] * List.formPerm [28, 33] * List.formPerm [31, 32] *
    List.formPerm [36, 44] * List.formPerm [37, 41] * List.formPerm [39, 43])

@[expose] def k1 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 1, 16, 21] * List.formPerm [2, 23] * List.formPerm [3, 5, 30, 37] *
    List.formPerm [4, 39, 8, 28] * List.formPerm [6, 7, 44, 32] * List.formPerm [9, 11, 36, 31] *
    List.formPerm [10, 33, 14, 43] * List.formPerm [12, 13, 26, 41] *
    List.formPerm [17, 20, 22, 24] * List.formPerm [18, 19] * List.formPerm [25, 42, 38, 40] *
    List.formPerm [27, 29, 34, 35])

@[expose] def k2 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 11] * List.formPerm [4, 9] * List.formPerm [5, 10] *
    List.formPerm [6, 14] * List.formPerm [7, 12] * List.formPerm [8, 13] *
    List.formPerm [15, 25] * List.formPerm [16, 34] * List.formPerm [17, 32] *
    List.formPerm [18, 33] * List.formPerm [19, 28] * List.formPerm [20, 26] *
    List.formPerm [21, 27] * List.formPerm [22, 31] * List.formPerm [23, 29] *
    List.formPerm [24, 30])

@[expose] def fixCnt (a : P45) : ℕ := (Finset.univ.filter fun i : Fin 45 => a i = i).card

@[expose] def cntL (L : List P45) (a : P45) : ℕ :=
  (L.filter fun g => decide (g * a = a * g)).length

@[expose] def reps (_ : Unit := ()) : List P45 :=
  [Certificates.OmegaT0.z0 (), Certificates.OmegaT0.yB (), r3 (), r4 ()]

@[expose] def repChk (A0 P0 : List P45) : Bool :=
  let z := Certificates.OmegaT0.z0 ()
  let y := Certificates.OmegaT0.yB ()
  let a := r3 ()
  let b := r4 ()
  (reps ()).all (fun r => decide (r ∈ A0) && decide (r * r = 1 ∧ r ≠ 1)) &&
    decide (z ∈ P0) && decide (y ∈ P0) && !decide (a ∈ P0) && !decide (b ∈ P0) &&
    decide (cntL A0 z = 1152 ∧ cntL A0 y = 192 ∧ cntL A0 a = 96 ∧ cntL A0 b = 1440) &&
    decide (fixCnt z = 13 ∧ fixCnt y = 5 ∧ fixCnt a = 7 ∧ fixCnt b = 15)

@[expose] def coverAll (rs A0 P0 : List P45) : Bool :=
  A0.all fun t => !decide (t * t = 1 ∧ t ≠ 1) ||
    P0.any fun g => rs.any fun r => decide (g * t * g⁻¹ = r)

@[expose] def d0List (P0 : List P45) (y : P45) : List P45 :=
  P0.filter fun g => decide (g * y = y * g)

@[expose] def k0List (_ : Unit := ()) : List P45 :=
  Certificates.OmegaF1051.closeL [k1 (), k2 ()] 16 [1]

@[expose] def layerChk (P0 : List P45) (y : P45) : Bool :=
  let D := d0List P0 y
  let K := k0List ()
  decide (D.length = 720) && decide (K.length = 120 ∧ K.Nodup) && decide ((1 : P45) ∈ K) &&
    (K.all fun a => decide (a⁻¹ ∈ K) && K.all fun b => decide (a * b ∈ K)) &&
    (K.all fun a => decide (a ∈ D)) &&
    D.all fun d => decide (d = 1) || D.any fun g => !decide (g * d * g⁻¹ ∈ K)

@[expose] def check (_ : Unit := ()) : Bool :=
  let A0 := elemsT QA45
  let P0 := elemsT QP45
  repChk A0 P0 && coverAll (reps ()) A0 P0 && layerChk P0 (r4 ())

end Certificates.OmegaInv
