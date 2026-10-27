module

public import CFSG.GH74.KGroups.CoverJ3Check
public import Certificates.Data.Kernel.OpsK
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2

public section

namespace CFSG.KC.CovJ3

open CFSG.SectionRank.Native CFSG.GH74.KGroups.J3 CFSG.KC.OpsK

variable {V : Type} (O : Ops Nat V)

@[expose] def letterT (A B B2 : Nat) (z : ℤ) : Nat :=
  if z = 1 ∨ z = -1 then A else if z = 2 then B else if z = -2 then B2 else O.one

@[expose] def wordT (A B B2 : Nat) (w : List ℤ) : Nat :=
  (w.map (letterT O A B B2)).foldr O.mul O.one

@[expose] def xT (A B B2 : Nat) (ws : List (List ℤ)) (i : Nat) : Nat :=
  O.mul (O.mul (wordT O A B B2 (ws.getD (2 ^ i - 1) [])) A)
    (wordT O A B B2 (invWord (ws.getD (2 ^ i - 1) [])))

@[expose] noncomputable def bodyT (A B B2 : Nat) (ws : List (List ℤ)) (tests : List ℕ) (x0 x1 x2 x3 : Nat) :
    Bool :=
  O.eq (O.mul A A) O.one && O.eq (O.mul B B2) O.one && decide (ws.length = 15) &&
    (List.range 15).all (fun k =>
      forceB (wordT O A B B2 (ws.getD k [])) fun g =>
        forceB (wordT O A B B2 (invWord (ws.getD k []))) fun gi =>
          O.eq (O.mul g gi) O.one && O.eq (O.mul gi g) O.one &&
            O.eq (O.mul g x0) (O.mul (prodBase2 O [x0, x1, x2, x3] (k + 1)) g)) &&
    [x0, x1, x2, x3].all (fun X => O.eq (O.mul X X) O.one) && O.commsOK [x0, x1, x2, x3] &&
    O.kerModOK O.one [x0, x1, x2, x3] tests

@[expose] noncomputable def conjT (A B : Nat) (ws : List (List ℤ)) (tests : List ℕ) : Bool :=
  forceB (O.mul B B) fun B2 =>
    forceB (xT O A B B2 ws 0) fun x0 => forceB (xT O A B B2 ws 1) fun x1 =>
      forceB (xT O A B B2 ws 2) fun x2 => forceB (xT O A B B2 ws 3) fun x3 =>
        bodyT O A B B2 ws tests x0 x1 x2 x3

end CFSG.KC.CovJ3

end
