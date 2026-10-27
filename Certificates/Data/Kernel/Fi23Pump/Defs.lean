module

public import Certificates.Data.Kernel.Fi23Q.Defs
public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Pump

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Fi23R

@[expose] noncomputable def yK (G : Nat → Nat) (y t : List Nat) : Bool :=
  bAnd(eqH G (powW (nat_lit 5) y) List.nil, bAnd(Bool.not (eqH G y List.nil),
    eqH G (List.append y t) (List.append t y)))

@[expose] noncomputable def recP (P i : Nat) : Nat :=
  fld(P, Nat.mul (nat_lit 32) i, nat_lit 4294967295)

@[expose] noncomputable def ptE (e : Nat) : Nat := Nat.land e (nat_lit 32767)

@[expose] noncomputable def depE (e : Nat) : Nat := fld(e, nat_lit 15, nat_lit 31)

@[expose] noncomputable def genW (G : Nat → Nat) (u v : List Nat) (g q : Nat) : Nat :=
  nIf(Nat.beq g (nat_lit 0), wv G u q, wv G v q)

@[expose] noncomputable def rowE (G : Nat → Nat) (u v : List Nat) (N r e j e' : Nat) : Bool :=
  bAnd(Nat.blt j N, bAnd(Nat.beq (Nat.succ (depE e')) (depE e),
    Nat.beq (genW G u v (Nat.shiftRight e (nat_lit 31)) (ptE e')) (ptE e)))

@[expose] noncomputable def rowK (G : Nat → Nat) (u v : List Nat) (P N r i : Nat) : Bool :=
  strictB (recP P i) fun e => bAnd(Nat.blt (ptE e) (nat_lit 31671),
    bIf(Nat.beq (depE e) (nat_lit 0), Nat.beq (ptE e) r,
      strictB (fld(e, nat_lit 20, nat_lit 2047)) fun j => strictB (recP P j) fun e' =>
        rowE G u v N r e j e'))

@[expose] noncomputable def incK (P i : Nat) : Bool :=
  Nat.blt (ptE (recP P i)) (ptE (recP P (Nat.succ i)))

@[expose] noncomputable def orbK (G : Nat → Nat) (u v : List Nat) (P N r : Nat) : Bool :=
  bAnd(allN N (rowK G u v P N r), allN (Nat.sub N (nat_lit 1)) (incK P))

end CFSG.KC.Fi23Pump

end
