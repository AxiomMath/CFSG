module

public import Certificates.Data.PSp43Sylow
public import Certificates.Data.P43Twin

public section

namespace Certificates.OmegaB0

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def b0 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 9] * List.formPerm [4, 10] * List.formPerm [5, 11] *
    List.formPerm [6, 12] * List.formPerm [7, 13] * List.formPerm [8, 14] *
    List.formPerm [25, 35] * List.formPerm [26, 44] * List.formPerm [27, 42] *
    List.formPerm [28, 43] * List.formPerm [29, 38] * List.formPerm [30, 36] *
    List.formPerm [31, 37] * List.formPerm [32, 41] * List.formPerm [33, 39] *
    List.formPerm [34, 40])

@[expose] def b1 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 23] * List.formPerm [2, 21] * List.formPerm [4, 37] *
    List.formPerm [5, 28] * List.formPerm [7, 39] * List.formPerm [8, 32] *
    List.formPerm [10, 31] * List.formPerm [11, 43] * List.formPerm [13, 33] *
    List.formPerm [14, 41] * List.formPerm [17, 18] * List.formPerm [19, 22] *
    List.formPerm [25, 40] * List.formPerm [26, 36] * List.formPerm [30, 44] *
    List.formPerm [34, 35])

@[expose] def b2 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 19] * List.formPerm [2, 17] * List.formPerm [3, 42] *
    List.formPerm [4, 33] * List.formPerm [6, 38] * List.formPerm [7, 31] * List.formPerm [9, 27] *
    List.formPerm [10, 39] * List.formPerm [12, 29] * List.formPerm [13, 37] *
    List.formPerm [18, 21] * List.formPerm [22, 23] * List.formPerm [25, 36] *
    List.formPerm [26, 40] * List.formPerm [30, 35] * List.formPerm [34, 44])

@[expose] def b3 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 18] * List.formPerm [2, 22] * List.formPerm [3, 29] *
    List.formPerm [5, 41] * List.formPerm [6, 27] * List.formPerm [8, 43] * List.formPerm [9, 38] *
    List.formPerm [11, 32] * List.formPerm [12, 42] * List.formPerm [14, 28] *
    List.formPerm [17, 23] * List.formPerm [19, 21] * List.formPerm [25, 44] *
    List.formPerm [26, 35] * List.formPerm [30, 40] * List.formPerm [34, 36])

@[expose] def b4 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [4, 7] * List.formPerm [5, 8] *
    List.formPerm [9, 12] * List.formPerm [10, 13] * List.formPerm [11, 14] *
    List.formPerm [17, 19] * List.formPerm [18, 22] * List.formPerm [21, 23] *
    List.formPerm [27, 29] * List.formPerm [28, 32] * List.formPerm [31, 33] *
    List.formPerm [37, 39] * List.formPerm [38, 42] * List.formPerm [41, 43])

@[expose] def bl (_ : Unit := ()) : List P45 := [b0 (), b1 (), b2 (), b3 (), b4 ()]

@[expose] def vecOfNat (n : ℕ) : Fin 5 → ZMod 2 :=
  fun i => if (n / 2 ^ (i : ℕ)) % 2 = 1 then 1 else 0

@[expose] def allVecs (_ : Unit := ()) : List (Fin 5 → ZMod 2) :=
  (List.range 32).map fun n => vecOfNat ((n + 1) % 32)

@[expose] def vcode (v : Fin 5 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val + 16 * (v 4).val

@[expose] def phiTable (B : List P45) : Array P45 :=
  ((List.range 32).map fun n =>
    tab (((List.finRange 5).map fun j =>
      if vecOfNat n j = 1 then B.getD (j : ℕ) 1 else 1).prod)).toArray

@[expose] def phi0 (Φ : Array P45) (v : Fin 5 → ZMod 2) : P45 := Φ.getD (vcode v) 1

@[expose] def bElems (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) : List P45 :=
  (allV.filter fun v => decide (∑ i, v i = 0)).map (phi0 Φ)

@[expose] def normB (Bl : List P45) (n : P45) : Bool :=
  Bl.all fun b => decide (n * b * n⁻¹ ∈ Bl) && decide (n⁻¹ * b * n ∈ Bl)

@[expose] def s5l (_ : Unit := ()) : List (Equiv.Perm (Fin 5)) :=
  [1, Equiv.swap (0 : Fin 5) 1].flatMap fun a =>
    [1, Equiv.swap (0 : Fin 5) 2, Equiv.swap 1 2].flatMap fun b =>
      [1, Equiv.swap (0 : Fin 5) 3, Equiv.swap 1 3, Equiv.swap 2 3].flatMap fun c =>
        [1, Equiv.swap (0 : Fin 5) 4, Equiv.swap 1 4, Equiv.swap 2 4, Equiv.swap 3 4].map fun d =>
          a * b * c * d

@[expose] def closedChk (Bl : List P45) : Bool :=
  decide (Bl.length = 16 ∧ Bl.Nodup) && decide ((1 : P45) ∈ Bl) &&
    Bl.all fun a => decide (a⁻¹ ∈ Bl) && decide (a * a = 1) &&
      Bl.all fun b => decide (a * b ∈ Bl) && decide (a * b = b * a)

@[expose] def sylowChk (T Bl : List P45) : Bool :=
  Bl.all (fun b => decide (b ∈ T)) &&
    T.all fun a => decide (a ∈ Bl) ||
      (let C := T.filter fun g => decide (g * a = a * g)
       decide (C.length ≤ 16) &&
        (decide (C.length < 16) || C.any fun x => C.any fun y => decide (x * y ≠ y * x)))

@[expose] def centChk (A0 Bl : List P45) : Bool :=
  A0.all fun a => !(Bl.all fun b => decide (a * b = b * a)) || decide (a ∈ Bl)

@[expose] def vecChk (allV : List (Fin 5 → ZMod 2)) (S5 : List (Equiv.Perm (Fin 5))) : Bool :=
  decide (∀ v : Fin 5 → ZMod 2, v ∈ allV) && decide (∀ σ : Equiv.Perm (Fin 5), σ ∈ S5)

@[expose] def homChk (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) : Bool :=
  allV.all fun v => allV.all fun w =>
    decide (phi0 Φ (v + w) = phi0 Φ v * phi0 Φ w) &&
      (!(decide (∑ i, v i = 0) && decide (∑ i, w i = 0) && decide (phi0 Φ v = phi0 Φ w)) ||
        decide (v = w))

@[expose] def actEq (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) (n : P45)
    (σ : Equiv.Perm (Fin 5)) : Bool :=
  allV.all fun v => decide (n * phi0 Φ v * n⁻¹ = phi0 Φ (v ∘ σ.symm))

@[expose] def conjIdx (bs : List P45) (n : P45) : List ℕ :=
  bs.map fun b => bs.findIdx fun c => decide (n * b * n⁻¹ = c)

@[expose] def matchIdx (τ : List ℕ) (σ : Equiv.Perm (Fin 5)) : Bool :=
  (List.finRange 5).all fun j => decide ((σ j : ℕ) = τ.getD (j : ℕ) 5)

@[expose] def actChk (L0 A0 bs : List P45) (Φ : Array P45) (Bl : List P45)
    (allV : List (Fin 5 → ZMod 2)) (S5 : List (Equiv.Perm (Fin 5))) : Bool :=
  let NP := L0.filter (normB Bl)
  (NP.all fun n => let τ := conjIdx bs n
    S5.any fun σ => matchIdx τ σ && decide (Equiv.Perm.sign σ = 1) && actEq Φ allV n σ) &&
    ((A0.filter (normB Bl)).all fun n => let τ := conjIdx bs n
      S5.any fun σ => matchIdx τ σ && actEq Φ allV n σ) &&
    S5.all fun σ => !decide (Equiv.Perm.sign σ = 1) ||
      NP.any fun n => matchIdx (conjIdx bs n) σ && actEq Φ allV n σ

@[expose] def classChk (L0 : List P45) (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) : Bool :=
  let a := Certificates.P43Twin.tA ()
  let b := Certificates.P43Twin.tB ()
  allV.all fun v =>
    (!(decide (∑ i, v i = 0) && decide ((Finset.univ.filter fun i : Fin 5 => v i ≠ 0).card = 4)) ||
      L0.any fun c => decide (c * a * c⁻¹ = phi0 Φ v)) &&
    (!(decide (∑ i, v i = 0) && decide ((Finset.univ.filter fun i : Fin 5 => v i ≠ 0).card = 2)) ||
      L0.any fun c => decide (c * b * c⁻¹ = phi0 Φ v))

@[expose] def check (_ : Unit := ()) : Bool :=
  let L0 := elemsT QP45
  let A0 := elemsT QA45
  let T := elemsT QT0
  let bs := bl ()
  let Φ := phiTable bs
  let allV := allVecs ()
  let S5 := s5l ()
  let Bl := bElems Φ allV
  closedChk Bl && sylowChk T Bl && centChk A0 Bl && vecChk allV S5 && homChk Φ allV &&
    actChk L0 A0 bs Φ Bl allV S5 && classChk L0 Φ allV

end Certificates.OmegaB0
