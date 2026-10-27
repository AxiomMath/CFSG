module

public import Certificates.Data.Item434SporGenKit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG.Monster.B.Co2.Native

@[expose] def wab (n : ℕ) (ga gb : Array ℕ) (w : List ℤ) : Array ℕ :=
  wordA n #[ga, gb] #[invCand n ga, invCand n gb] w

@[expose] def wabs (n : ℕ) (ga gb : Array ℕ) (ws : List (List ℤ)) : Array (Array ℕ) :=
  (ws.map (wab n ga gb)).toArray

@[expose] def wordsOK (j : ℕ) (ws : List (List ℤ)) : Bool := ws.all (lettersOK j)

@[expose] def fixWordsCheck (n : ℕ) (ga gb : Array ℕ) (sw : List (List ℤ)) (ords : List ℕ)
    (ps : List (ℕ × ℕ)) (e₁ e₂ : Array ℕ) (wa wb : List ℤ) : Bool :=
  let Sg := wabs n ga gb sw
  let Si := Sg.map (invCand n)
  isInvA n ga (invCand n ga) && isInvA n gb (invCand n gb) && wordsOK 2 sw &&
    allLt Sg.size (fun i => isInvA n Sg[i]! Si[i]!) &&
    lettersOK Sg.size wa && lettersOK Sg.size wb &&
    eqA n ga (wordA n Sg Si wa) && eqA n gb (wordA n Sg Si wb) &&
    e9Check n e₁ e₂ && sigCheck n Sg ords ps e₁ e₂

structure FixData where
  sw : List (List ℤ)
  ords : List ℕ
  ps : List (ℕ × ℕ)
  wa : List ℤ
  wb : List ℤ

@[expose] def FixData.check (c : FixData) (n : ℕ) (ga gb e₁ e₂ : Array ℕ) : Bool :=
  fixWordsCheck n ga gb c.sw c.ords c.ps e₁ e₂ c.wa c.wb

@[expose] def cmA (n : ℕ) (x y : Array ℕ) : Array ℕ :=
  compA n (compA n x y) (compA n (invCand n x) (invCand n y))

@[expose] def heisCheck (n : ℕ) (x y : Array ℕ) : Bool :=
  isInvA n x (invCand n x) && isInvA n y (invCand n y) &&
    eqA n (powN n x 3) (idA n) && eqA n (powN n y 3) (idA n) &&
    commN n (cmA n x y) x && commN n (cmA n x y) y && !eqA n (cmA n x y) (idA n)

@[expose] def ex27E2 (n : ℕ) (x y : Array ℕ) (i : ℕ) : Array ℕ :=
  if i = 0 then x else if i = 1 then y else if i = 2 then compA n x y
  else compA n x (powN n y 2)

@[expose] def ex27Check (n : ℕ) (ga gb : Array ℕ) (xw yw : List ℤ) (c₀ c₁ c₂ c₃ : FixData) :
    Bool :=
  let x := wab n ga gb xw
  let y := wab n ga gb yw
  isInvA n ga (invCand n ga) && isInvA n gb (invCand n gb) &&
    lettersOK 2 xw && lettersOK 2 yw && heisCheck n x y &&
    c₀.check n ga gb (cmA n x y) (ex27E2 n x y 0) &&
    c₁.check n ga gb (cmA n x y) (ex27E2 n x y 1) &&
    c₂.check n ga gb (cmA n x y) (ex27E2 n x y 2) &&
    c₃.check n ga gb (cmA n x y) (ex27E2 n x y 3)

@[expose] def sylow9Check (n : ℕ) (ga gb : Array ℕ) (e1w e2w : List ℤ) (c : FixData) : Bool :=
  isInvA n ga (invCand n ga) && isInvA n gb (invCand n gb) &&
    lettersOK 2 e1w && lettersOK 2 e2w && c.check n ga gb (wab n ga gb e1w) (wab n ga gb e2w)

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
