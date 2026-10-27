module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Pc3

open CFSG.KC.Enum

@[expose] noncomputable def dg (u k : Nat) : Nat := fld(u, Nat.shiftLeft k (nat_lit 1), nat_lit 3)

@[expose] noncomputable def f32 (T k : Nat) : Nat :=
  fld(T, Nat.shiftLeft k (nat_lit 5), nat_lit 4294967295)

@[expose] noncomputable def lowV (u k : Nat) : Nat :=
  Nat.land u (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft k (nat_lit 1))) (nat_lit 1))

@[expose] noncomputable def highV (u k : Nat) : Nat :=
  Nat.shiftLeft (Nat.shiftRight u (Nat.shiftLeft (Nat.succ k) (nat_lit 1)))
    (Nat.shiftLeft (Nat.succ k) (nat_lit 1))

@[expose] noncomputable def rep (e : Nat) (g : Nat → Nat) (s : Nat) : Nat :=
  nIf(Nat.beq e (nat_lit 0), s, strictN (g s) fun s₁ => nIf(Nat.beq e (nat_lit 1), s₁, g s₁))

@[expose] noncomputable def mulW (M : Nat → Nat → Nat) (n x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun j acc => strictN acc fun a => rep (dg y j) (M j) a) n

@[expose] noncomputable def conjT (M : Nat → Nat → Nat) (CJ n k t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc fun a =>
      rep (dg t j) (fun s => mulW M n s (f32 CJ (Nat.add (Nat.shiftLeft k (nat_lit 4)) j))) a) n

@[expose] noncomputable def mulG (PW CJ n f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ u => u)
    (fun _ M k u => strictN (conjT M CJ n k (highV u k)) fun c =>
      (fun e => nIf(Nat.beq e (nat_lit 2), Nat.add (lowV u k) (mulW M n (f32 PW k) c),
        Nat.add (Nat.add (lowV u k) (Nat.shiftLeft (Nat.succ e) (Nat.shiftLeft k (nat_lit 1)))) c))
      (dg u k)) f

@[expose] noncomputable def mulV (PW CJ n u v : Nat) : Nat := mulW (mulG PW CJ n n) n u v

@[expose] noncomputable def vecOK (n u : Nat) : Bool :=
  bAnd(Nat.blt u (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft n (nat_lit 1))),
    Nat.beq (Nat.land (Nat.land u (Nat.shiftRight u (nat_lit 1))) (nat_lit 1431655765)) (nat_lit 0))

@[expose] noncomputable def pcDataOK (n PW CJ : Nat) : Bool :=
  bAnd(Nat.ble n (nat_lit 16),
    allN n fun k => strictB (f32 PW k) fun w => bAnd(vecOK n w,
      bAnd(Nat.beq (lowV w (Nat.succ k)) (nat_lit 0),
        allN n fun j => bIf(Nat.blt k j,
          strictB (f32 CJ (Nat.add (Nat.shiftLeft k (nat_lit 4)) j)) fun c => bAnd(vecOK n c,
            Nat.beq (lowV c (Nat.succ j)) (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft j (nat_lit 1)))),
          true))))

end CFSG.KC.Pc3

end
