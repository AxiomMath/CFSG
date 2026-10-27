module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace Certificates.Asc82Fbar

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.HarrisLit.P1

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

@[expose] def slCode (A : SL23) : ℕ :=
  27 * (A.1 0 0).val + 9 * (A.1 0 1).val + 3 * (A.1 1 0).val + (A.1 1 1).val

@[expose] def slList (_ : Unit := ()) : List SL23 :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b =>
    (List.range 3).flatMap fun c => (List.range 3).filterMap fun d =>
      if h : (a : ZMod 3) * d - b * c = 1 then
        some ⟨!![(a : ZMod 3), b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩
      else none

@[expose] def rhoT (n : Nat) (rho : List Table) (A : SL23) : Table := rho.getD (slCode A) (idT n)

structure InnerData where
  b : Table
  c : Table
  r₁ : Table
  r₂ : Table

structure OuterData where
  b : Table
  c : Table
  run : Nat
  row : Nat
  rho : List Table

@[expose] def allInvConj (n : Nat) (E : Array Table) (b : Table) : Bool :=
  E.all fun x => !involOK n x || E.any fun l => tblEq n (compT n x l) (compT n l b)

@[expose] def innerOK (n cap : Nat) (sift : Table → Bool) (t l₁ l₂ : Table) (d : InnerData) :
    Bool :=
  let E := (mulClosureH n [l₁, l₂].toArray cap).1
  let ci := invT n d.c
  enumOK n cap 360 [l₁, l₂] && permOK n d.b && involOK n d.b && memT n E d.b &&
    allInvConj n E d.b && permOK n d.c && invOK n d.c ci && sift d.c &&
    tblEq n (compT n d.c t) (compT n d.b d.c) &&
    permOK n (conjT n d.c ci l₁) && permOK n (conjT n d.c ci l₂) &&
    centCount n cap [l₁, l₂] [d.b, conjT n d.c ci l₁, conjT n d.c ci l₂] ≤ 2 &&
    [d.r₁, d.r₂].all (fun r => permOK n r && involOK n r && memT n E r && commTT n r d.b) &&
    enumOK n cap 8 [d.r₁, d.r₂]

@[expose] def pocketOK (n cap : Nat) (gs : List Table) (t₂ : Table) (rho : List Table) : Bool :=
  let S := slList ()
  let Kl := S.map (rhoT n rho)
  let EM := (mulClosureH n gs.toArray cap).1
  rho.length == 81 && rho.all (permOK n) &&
    S.all (fun A => S.all fun B =>
      tblEq n (compT n (rhoT n rho A) (rhoT n rho B)) (rhoT n rho (A * B))) &&
    S.all (fun A => !tblEq n (rhoT n rho A) (idT n) || decide (A = 1)) &&
    S.any (fun A => tblEq n (rhoT n rho A) t₂) && Kl.all (memT n EM) &&
    enumOK n cap 24 Kl && normOK n cap Kl gs

@[expose] def outerOK (n cap : Nat) (sift : Table → Bool) (runs : List Run) (l₁ l₂ : Table)
    (d : OuterData) : Bool :=
  let E := (mulClosureH n [l₁, l₂].toArray cap).1
  match (runs[d.run]?).bind fun R => R.rows[d.row]? with
  | some ⟨⟨t₂, _, _, _, _, _, _⟩, .small gs _⟩ =>
      enumOK n cap 360 [l₁, l₂] && permOK n d.b && involOK n d.b && memT n E d.b &&
        allInvConj n E d.b && permOK n d.c && sift d.c &&
        tblEq n (compT n d.c t₂) (compT n d.b d.c) && pocketOK n cap gs t₂ d.rho
  | _ => false

@[expose] def rowFbarOK (n cap : Nat) (sift : Table → Bool) (runs : List Run)
    (inn : InnerData) (out : OuterData) (r : Row) : Bool :=
  match r.kind with
  | .five _ ord => ord % 16 == 0 && r.row.centOrder % 25 != 0
  | .a6 l₁ l₂ _ =>
      if r.row.outer then outerOK n cap sift runs l₁ l₂ out
      else innerOK n cap sift r.row.rep l₁ l₂ inn
  | _ => true

@[expose] def fbarCheck (n cap : Nat) (sift : Table → Bool) (runs : List Run)
    (inn : InnerData) (out : OuterData) : Bool :=
  runs.all fun R => R.rows.all (rowFbarOK n cap sift runs inn out)

end Certificates.Asc82Fbar
