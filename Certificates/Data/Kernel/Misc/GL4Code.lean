module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.GL4

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def mul4F (a b : Nat) : Nat :=
  CFSG.KC.Misc.letN a fun a => CFSG.KC.Misc.letN b fun b =>
    Nat.xor (Nat.xor (Nat.xor
      (Nat.land (Nat.mul (Nat.land a (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land b (nat_lit 15)) (nat_lit 4369)))
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (nat_lit 1)) (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land (Nat.shiftRight b (nat_lit 4)) (nat_lit 15)) (nat_lit 4369))))
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (nat_lit 2)) (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land (Nat.shiftRight b (nat_lit 8)) (nat_lit 15)) (nat_lit 4369))))
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (nat_lit 3)) (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land (Nat.shiftRight b (nat_lit 12)) (nat_lit 15)) (nat_lit 4369)))

@[expose] noncomputable def id4 : Nat := nat_lit 33825

@[expose] noncomputable def fld (x o w : Nat) : Nat :=
  Nat.mod (Nat.shiftRight x o) (Nat.shiftLeft (nat_lit 1) w)

@[expose] noncomputable def covAtM (M : Nat → Nat → Nat) (EP EA RA W : Nat → Nat) (N nR k : Nat) :
    Bool :=
  letB (W k) fun w => letB (fld w (nat_lit 0) (nat_lit 12)) fun p =>
    letB (fld w (nat_lit 12) (nat_lit 12)) fun q => letB (Nat.shiftRight w (nat_lit 24)) fun j =>
      andB (Nat.blt p N) (andB (Nat.blt q N) (andB (Nat.blt j nR)
        (Nat.beq (M (M (EP p) (EA (RA j))) (EP q)) (EA k))))

@[expose] noncomputable def wIdx (X l : Nat) : Nat :=
  fld X (Nat.add (nat_lit 5) (Nat.mul (nat_lit 12) l)) (nat_lit 12)

@[expose] noncomputable def wValM (M : Nat → Nat → Nat) (EP : Nat → Nat) (r X n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (EP (wIdx X (nat_lit 0)))
    (fun l acc => M (M acc r) (EP (wIdx X (Nat.succ l)))) n

@[expose] noncomputable def wordOKM (M : Nat → Nat → Nat) (EP : Nat → Nat) (N r g X : Nat) : Bool :=
  letB (fld X (nat_lit 0) (nat_lit 5)) fun c =>
    andB (Nat.blt (nat_lit 0) c) (andB (allN c fun l => Nat.blt (wIdx X l) N)
      (Nat.beq (wValM M EP r X (Nat.pred c)) g))

@[expose] noncomputable def joinAtM (M : Nat → Nat → Nat) (EP : Nat → Nat) (N : Nat)
    (G : Nat → Nat) (nG : Nat) (EA : Nat → Nat) (NA : Nat) (EQ : Nat → Nat → Nat) (nT : Nat)
    (NQ NGQ : Nat → Nat) (GQ : Nat → Nat → Nat) (R : Nat) (WX : Nat → Nat) : Bool :=
  letB (fld R (nat_lit 0) (nat_lit 15)) fun a => letB (fld R (nat_lit 15) (nat_lit 6)) fun t =>
    letB (fld R (nat_lit 21) (nat_lit 15)) fun x => letB (EA a) fun r =>
      andB (Nat.blt a NA) (andB (Nat.blt t nT)
        (andB (andB (Nat.blt x (NQ t)) (Nat.beq (EQ t x) r))
          (andB (allN nG fun i => letB (fld R (Nat.add (nat_lit 36) (Nat.mul (nat_lit 15) i))
              (nat_lit 15)) fun y => andB (Nat.blt y (NQ t)) (Nat.beq (EQ t y) (G i)))
            (allN (NGQ t) fun i => wordOKM M EP N r (GQ t i) (WX i)))))

end CFSG.KC.Misc.GL4

end
