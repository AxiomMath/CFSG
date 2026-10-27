module

public import Certificates.Data.OmegaT0

public section

namespace Certificates.OmegaF1051

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def gq1 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 10, 2, 13] * List.formPerm [3, 32, 6, 28] *
    List.formPerm [4, 22, 7, 18] * List.formPerm [5, 42, 8, 38] * List.formPerm [9, 11, 12, 14] *
    List.formPerm [15, 20] * List.formPerm [16, 24] * List.formPerm [17, 33, 19, 31] *
    List.formPerm [21, 37, 23, 39] * List.formPerm [25, 30] * List.formPerm [26, 34] *
    List.formPerm [27, 43, 29, 41] * List.formPerm [35, 40] * List.formPerm [36, 44])

@[expose] def gq2 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 12, 2, 9] * List.formPerm [3, 23, 6, 21] * List.formPerm [4, 43, 7, 41] *
    List.formPerm [5, 33, 8, 31] * List.formPerm [10, 11, 13, 14] * List.formPerm [15, 16] *
    List.formPerm [17, 38, 19, 42] * List.formPerm [18, 29, 22, 27] * List.formPerm [20, 24] *
    List.formPerm [25, 26] * List.formPerm [28, 39, 32, 37] * List.formPerm [30, 34] *
    List.formPerm [35, 36] * List.formPerm [40, 44])

@[expose] def gq3 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 6, 2, 3] * List.formPerm [4, 5, 7, 8] * List.formPerm [9, 23, 12, 21] *
    List.formPerm [10, 28, 13, 32] * List.formPerm [11, 39, 14, 37] * List.formPerm [15, 16] *
    List.formPerm [17, 29, 19, 27] * List.formPerm [18, 38, 22, 42] * List.formPerm [20, 24] *
    List.formPerm [25, 30] * List.formPerm [26, 34] * List.formPerm [31, 43, 33, 41] *
    List.formPerm [35, 44] * List.formPerm [36, 40])

@[expose] def gq4 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 5, 2, 8] * List.formPerm [3, 7, 6, 4] * List.formPerm [9, 31, 12, 33] *
    List.formPerm [10, 42, 13, 38] * List.formPerm [11, 17, 14, 19] * List.formPerm [15, 24] *
    List.formPerm [16, 20] * List.formPerm [18, 28, 22, 32] * List.formPerm [21, 43, 23, 41] *
    List.formPerm [25, 26] * List.formPerm [27, 37, 29, 39] * List.formPerm [30, 34] *
    List.formPerm [35, 40] * List.formPerm [36, 44])

@[expose] def stepL (gens S : List P45) : List P45 :=
  S.foldl (fun acc s => gens.foldl (fun acc' g =>
    if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc) S

@[expose] def closeL (gens : List P45) : ℕ → List P45 → List P45
  | 0, S => S
  | n + 1, S => closeL gens n (stepL gens S)

@[expose] def q0l (_ : Unit := ()) : List P45 :=
  closeL [gq1 (), gq2 (), gq3 (), gq4 ()] 6 [1]

@[expose] def centL (L : List P45) (t : P45) : List P45 :=
  L.filter fun g => decide (g * t = t * g)

@[expose] def oddL (C : List P45) : List P45 :=
  C.filter fun x => decide (x ^ 9 = 1)

@[expose] def zChk (T : List P45) (z : P45) : Bool :=
  decide (z * z = 1 ∧ z ≠ 1) && decide (z ∈ T) && T.all fun t => decide (t * z = z * t)

@[expose] def closedChk (Q : List P45) : Bool :=
  decide (Q.length = 32 ∧ Q.Nodup) && decide ((1 : P45) ∈ Q) &&
    Q.all fun a => decide (a⁻¹ ∈ Q) && Q.all fun b => decide (a * b ∈ Q)

@[expose] def inOTwoChk (Q O : List P45) (z : P45) : Bool :=
  let P2 := O.flatMap fun b => O.map fun c => b * c
  (Q.all fun q => decide (q ∈ P2) || decide (q = z)) && O.any fun a => decide (a⁻¹ * z ∈ P2)

@[expose] def normChk (CA Q : List P45) : Bool :=
  CA.all fun c => Q.all fun q => decide (c * q * c⁻¹ ∈ Q)

@[expose] def dList (Q : List P45) (z u : P45) : List P45 :=
  Q.filter fun q => decide (q * u * q⁻¹ * u⁻¹ = 1 ∨ q * u * q⁻¹ * u⁻¹ = z)

@[expose] def oneChk (Q B : List P45) (z : P45) : Bool :=
  B.all fun u => decide (2 * (dList Q z u).length < 32)

@[expose] def twoChk (Q B : List P45) (z : P45) : Bool :=
  B.all fun u1 =>
    let D1 := dList Q z u1
    B.all fun u2 =>
      decide (u1⁻¹ * u2 ∈ Q) || !decide (u1 * u2 * u1⁻¹ * u2⁻¹ ∈ Q) ||
        decide (4 * (dList D1 z u2).length < 32)

@[expose] def check (_ : Unit := ()) : Bool :=
  let L0 := elemsT QP45
  let A0 := elemsT QA45
  let T := elemsT QT0
  let z := Certificates.OmegaT0.z0 ()
  let Q := q0l ()
  let CA := centL A0 z
  let Cl := centL L0 z
  let B := CA.filter fun u => !decide (u ∈ Q) && decide (u * u ∈ Q)
  zChk T z && decide (CA.length = 1152) && decide (Cl.length = 576) && closedChk Q &&
    inOTwoChk Q (oddL Cl) z && normChk CA Q && oneChk Q B z && twoChk Q B z

end Certificates.OmegaF1051
