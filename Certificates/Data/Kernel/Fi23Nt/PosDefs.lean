module

public import Certificates.Data.Kernel.Fi23K.Defs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def rootK (PAR : Nat → Nat) (f : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 0))
    (fun _ ih k => bIf(Nat.beq k (nat_lit 0), true, ih (PAR k))) f

@[expose] noncomputable def edgeK (G PTS PAR LAB : Nat → Nat) (k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), Nat.beq (PTS (nat_lit 0)) (nat_lit 0),
    bAnd(Nat.blt (PAR k) (nat_lit 31671), bAnd(Nat.blt (LAB k) (nat_lit 24),
      Nat.beq (tb G (Nat.add (nat_lit 52) (LAB k)) (PTS (PAR k))) (PTS k))))

@[expose] noncomputable def posK (G POS PTS PAR LAB : Nat → Nat) (x : Nat) : Bool :=
  bAnd(strictB (POS x) fun k => bAnd(Nat.blt k (nat_lit 31671), Nat.beq (PTS k) x),
    bAnd(rootK PAR (nat_lit 20) x, edgeK G PTS PAR LAB x))

@[expose] noncomputable def posSlK (G POS PTS PAR LAB : Nat → Nat) (lo len : Nat) : Bool :=
  allBlk lo (posK G POS PTS PAR LAB) len

@[expose] noncomputable def wokK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(bAnd(Nat.ble (nat_lit 52) r, Nat.blt r (nat_lit 76)), ih)) w

@[expose] noncomputable def wsokK (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(wokK w, ih)) W

end CFSG.KC.Fi23Nt

end
