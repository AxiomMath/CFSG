module

public import Certificates.Data.Kernel.AE6Tri.DefsC

public section

namespace CFSG.KC.AE6E8

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.AE6Tri

@[expose] noncomputable def sumOK (S W : Nat → Nat) (G VL : List Nat) : Bool :=
  allIx VL (fun j i => bAnd(allN 16 (fun x =>
      Nat.beq (pg 9 (mask 9) (S j) x) (pg 5 (mask 5) (W j) x)),
    allN 360 (fun x => Nat.beq (pg 9 (mask 9) (S j) (Nat.add (nat_lit 16) x))
      (Nat.add (nat_lit 16) (pg 9 (mask 9) (gl G i) x))))) 0

@[expose] def piP : Nat := 547072003193943912156161

@[expose] noncomputable def wSel (T : Nat → Nat) (j : Nat) : Nat := nIf(Nat.blt j 7, T j, piP)

@[expose] noncomputable def q8OK (G w₁ w₂ : List Nat) : Bool :=
  strictB (awN G w₁) (fun X => strictB (awN G w₂) (fun Y => strictB (pmN 360 9 X X) (fun X2 =>
    bAnd(notB (eqN 360 9 X2 (pidn 360 9)), bAnd(eqN 360 9 (pmN 360 9 X2 X2) (pidn 360 9),
      bAnd(eqN 360 9 (pmN 360 9 Y Y) X2,
        bAnd(strictB (pmN 360 9 X Y) (fun XY => eqN 360 9 (pmN 360 9 XY XY) X2),
          bAnd(notB (eqN 360 9 Y X), notB (eqN 360 9 Y (pmN 360 9 X2 X))))))))))

end CFSG.KC.AE6E8

end
