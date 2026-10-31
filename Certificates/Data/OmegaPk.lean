module

public import Certificates.Data.P43Twin

public section

namespace Certificates.OmegaPk

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.TA3.Check Certificates.P43Twin

local notation "P45" => Equiv.Perm (Fin 45)

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

@[expose] def code (A : SL23) : ℕ :=
  27 * (A.1 0 0).val + 9 * (A.1 0 1).val + 3 * (A.1 1 0).val + (A.1 1 1).val

@[expose] def allSL (_ : Unit := ()) : List SL23 :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b =>
    (List.range 3).flatMap fun c => (List.range 3).filterMap fun d =>
      if h : (a : ZMod 3) * d - b * c = 1 then
        some ⟨!![(a : ZMod 3), b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩
      else none

@[expose] def evalW (s t : P45) (w : List Bool) : P45 :=
  w.foldl (fun r b => r * if b then t else s) 1

@[expose] def wordTab : List (ℕ × List Bool) :=
  [(15, [false, false, false]), (16, [false, false, false, true, true]),
    (17, [false, false, false, true]), (21, [false]), (22, [false, true]),
    (23, [false, true, true]), (28, []), (31, [true, false, true]),
    (34, [false, false, false, true, false]), (37, [true]), (41, [true, false, true, true]),
    (42, [false, false, true, true, false]), (46, [true, true]), (48, [true, false]),
    (53, [true, false, true, true, false]), (56, [false, false]), (59, [false, true, false]),
    (62, [false, true, true, false]), (65, [false, false, true, true]),
    (67, [true, true, false, true]), (69, [false, false, true, false]),
    (74, [false, false, true]), (75, [true, true, false]), (79, [false, true, true, false, true])]

@[expose] def rhoTab (_ : Unit := ()) : List P45 :=
  let s := a1 ()
  let t := (x2 ())⁻¹
  (List.range 81).map fun c =>
    tab (match wordTab.lookup c with
      | some w => evalW s t w
      | none => 1)

@[expose] def rhoOf (T : List P45) (A : SL23) : P45 := T.getD (code A) 1

@[expose] def cj (g x : P45) : P45 := g⁻¹ * x * g

@[expose] def g0 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [4, 7] * List.formPerm [5, 8] *
    List.formPerm [9, 12] * List.formPerm [10, 13] * List.formPerm [11, 14] *
    List.formPerm [17, 19] * List.formPerm [18, 22] * List.formPerm [21, 23] *
    List.formPerm [27, 29] * List.formPerm [28, 32] * List.formPerm [31, 33] *
    List.formPerm [37, 39] * List.formPerm [38, 42] * List.formPerm [41, 43])

@[expose] def lP (_ : Unit := ()) : List P45 := elemsT QP45

@[expose] def clA (_ : Unit := ()) : List P45 := centB (lP ()) (tA ())

@[expose] def clB (_ : Unit := ()) : List P45 := centB (lP ()) (tB ())

@[expose] def kbList (g : P45) (KA : List P45) : List P45 := KA.map fun x => tab (cj g x)

end Certificates.OmegaPk
