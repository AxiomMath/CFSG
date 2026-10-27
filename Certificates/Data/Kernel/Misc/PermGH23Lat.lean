module

public import Certificates.Data.Kernel.Misc.PermGH23

public section

namespace CFSG.KC.Misc.GH23

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def fld (x o w : Nat) : Nat :=
  Nat.mod (Nat.shiftRight x o) (Nat.shiftLeft (nat_lit 1) w)

@[expose] noncomputable def lane (L : Nat → Nat) (w per i : Nat) : Nat :=
  fld (L (Nat.div i per)) (Nat.mul w (Nat.mod i per)) w

@[expose] noncomputable def covAt (EP EA RA W : Nat → Nat) (N nR k : Nat) : Bool :=
  letB (W k) fun w => letB (fld w (nat_lit 0) (nat_lit 12)) fun p =>
    letB (fld w (nat_lit 12) (nat_lit 12)) fun q => letB (Nat.shiftRight w (nat_lit 24)) fun j =>
      andB (Nat.blt p N) (andB (Nat.blt q N) (andB (Nat.blt j nR)
        (Nat.beq (mul8 (mul8 (EP p) (EA (RA j))) (EP q)) (EA k))))

@[expose] noncomputable def wIdx (X l : Nat) : Nat :=
  fld X (Nat.add (nat_lit 5) (Nat.mul (nat_lit 12) l)) (nat_lit 12)

@[expose] noncomputable def wVal (EP : Nat → Nat) (r X n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (EP (wIdx X (nat_lit 0)))
    (fun l acc => mul8 (mul8 acc r) (EP (wIdx X (Nat.succ l)))) n

@[expose] noncomputable def wordOK (EP : Nat → Nat) (N r g X : Nat) : Bool :=
  letB (fld X (nat_lit 0) (nat_lit 5)) fun c =>
    andB (Nat.blt (nat_lit 0) c) (andB (allN c fun l => Nat.blt (wIdx X l) N)
      (Nat.beq (wVal EP r X (Nat.pred c)) g))

@[expose] noncomputable def joinAt (EP : Nat → Nat) (N : Nat) (G : Nat → Nat) (nG : Nat)
    (EA : Nat → Nat) (NA : Nat) (EQ : Nat → Nat → Nat) (NQ NGQ : Nat → Nat)
    (GQ : Nat → Nat → Nat) (R : Nat) (WX : Nat → Nat) : Bool :=
  letB (fld R (nat_lit 0) (nat_lit 15)) fun a => letB (fld R (nat_lit 15) (nat_lit 6)) fun t =>
    letB (fld R (nat_lit 21) (nat_lit 15)) fun x => letB (EA a) fun r =>
      andB (Nat.blt a NA) (andB (Nat.blt t (nat_lit 41))
        (andB (andB (Nat.blt x (NQ t)) (Nat.beq (EQ t x) r))
          (andB (allN nG fun i => letB (fld R (Nat.add (nat_lit 36) (Nat.mul (nat_lit 15) i))
              (nat_lit 15)) fun y => andB (Nat.blt y (NQ t)) (Nat.beq (EQ t y) (G i)))
            (allN (NGQ t) fun i => wordOK EP N r (GQ t i) (WX i)))))

end CFSG.KC.Misc.GH23

end
