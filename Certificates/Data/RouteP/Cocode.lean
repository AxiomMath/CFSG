module

public import Certificates.Data.RouteP.Objects

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def conjACols : List Nat := [1955, 772, 623, 1962, 75, 528, 797, 726, 518, 107, 1549]

@[expose] def conjBCols : List Nat := [2023, 713, 921, 1889, 1544, 315, 1477, 797, 929, 1747, 1340]

@[expose] def relEps : List Nat := [61, 1016, 0, 783, 1743, 1446, 0]

@[expose] def relLetters (_ : Unit := ()) : List (List Int) :=
  [[1, 1], [2, 2, 2], (List.replicate 23 [1, 2]).flatten,
    (List.replicate 12 [-1, -2, 1, 2]).flatten,
    (List.replicate 5 [-1, -2, -1, -2, 1, 2, 1, 2]).flatten,
    [1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2,
      1, -2, 1, 2, 1, -2, 1, -2],
    (List.replicate 4 [1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2]).flatten]

@[expose] def epsLetters : Nat → Nat → Nat → List Int
  | 0, _, _ => []
  | k + 1, s, m => (if m % 2 = 1 then [(s : Int) + 3] else []) ++ epsLetters k (s + 1) (m / 2)

@[expose] def epsWord (m : Nat) : List Int := epsLetters 11 0 m

@[expose] def cocodeLetter (tabs : Array Table) (ai bi : Table) (l : Int) : Table :=
  if l = 1 then tabs[aReg]! else if l = -1 then ai else if l = 2 then tabs[bReg]! else
  if l = -2 then bi else if 3 ≤ l ∧ l < 14 then tabs[epsReg (l - 3).toNat]! else idT degree

@[expose] def conjOK (tabs : Array Table) (ai bi : Table) (c : Int) (cols : List Nat) : Bool :=
  (List.range 11).all fun j =>
    eqTab degree (wordT degree (cocodeLetter tabs ai bi) [c, (j : Int) + 3, -c])
      (wordT degree (cocodeLetter tabs ai bi) (epsWord cols[j]!))

@[expose] def relOK (tabs : Array Table) (ai bi : Table) (rl : List (List Int)) : Bool :=
  (List.range 7).all fun i =>
    eqTab degree (wordT degree (cocodeLetter tabs ai bi) rl[i]!)
      (wordT degree (cocodeLetter tabs ai bi) (epsWord relEps[i]!))

@[expose] def cocodeOKAt (tabs : Array Table) : Bool :=
  let ai := invT degree tabs[aReg]!
  let bi := invT degree tabs[bReg]!
  let rl := relLetters ()
  invOK degree tabs[aReg]! ai && invOK degree tabs[bReg]! bi &&
    conjOK tabs ai bi 1 conjACols && conjOK tabs ai bi 2 conjBCols && relOK tabs ai bi rl

@[expose] def cocodeOK (_ : Unit := ()) : Bool := cocodeOKAt (objRun ()).1

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
