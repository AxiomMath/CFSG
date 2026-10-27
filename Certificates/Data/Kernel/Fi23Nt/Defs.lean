module

public import Certificates.Data.Kernel.Fi23K.Defs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def climb0 (PAR LAB G : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x,
      strictN (PAR k) fun p =>
        strictN (tb G (Nat.add (nat_lit 52) (Nat.xor (LAB k) (nat_lit 1))) x) fun y => ih p y))
    f

@[expose] noncomputable def relK (POS PAR LAB G : Nat → Nat) (v x : Nat) : Bool :=
  strictB (climb0 PAR LAB G (nat_lit 20) (POS v) x) fun y => Nat.beq (tb G (nat_lit 43) y) y

@[expose] noncomputable def passK (POS PAR LAB G : Nat → Nat) (S : List (List Nat × Bool))
    (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun s _ ih => bAnd(Bool.not (Bool.xor (relK POS PAR LAB G v (wv G s.1 v)) s.2), ih)) S

@[expose] noncomputable def cntK (POS PAR LAB G : Nat → Nat) (S : List (List Nat × Bool))
    (lo len : Nat) : Nat :=
  foldBlk lo (fun v c => nIf(passK POS PAR LAB G S v, Nat.succ c, c)) len (nat_lit 0)

@[expose] noncomputable def cntSlK (POS PAR LAB G : Nat → Nat) (S : List (List Nat × Bool))
    (lo len c : Nat) : Bool :=
  Nat.beq (cntK POS PAR LAB G S lo len) c

end CFSG.KC.Fi23Nt

end
