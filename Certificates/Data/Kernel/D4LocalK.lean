module

public import Certificates.Data.Kernel.B3S3K

public section

namespace CFSG.KC.D4Local

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K

@[expose] noncomputable def upowK (w m u k p : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), p, nIf(Nat.beq k (nat_lit 1), pg w m u p, pg w m u (pg w m u p)))

@[expose] noncomputable def yconjK (w m u y k p : Nat) : Nat :=
  upowK w m u k (pg w m y (upowK w m u (Nat.mod (Nat.sub (nat_lit 3) k) (nat_lit 3)) p))

@[expose] noncomputable def wordK (w m u y wc p : Nat) : Nat :=
  nIf(Nat.beq wc (nat_lit 0), yconjK w m u y (nat_lit 0) (yconjK w m u y (nat_lit 1) p),
    nIf(Nat.beq wc (nat_lit 1),
      yconjK w m u y (nat_lit 0) (yconjK w m u y (nat_lit 0) (yconjK w m u y (nat_lit 1) p)),
      nIf(Nat.beq wc (nat_lit 2),
        yconjK w m u y (nat_lit 0) (yconjK w m u y (nat_lit 1) (yconjK w m u y (nat_lit 2) p)),
        yconjK w m u y (nat_lit 0) (yconjK w m u y (nat_lit 2) (yconjK w m u y (nat_lit 1) p)))))

@[expose] noncomputable def periodGoK (f : Nat → Nat) (i : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih cur l => strictN (f cur) fun c => strictN (Nat.succ l) fun l' =>
      nIf(Nat.beq c i, l', ih c l')) fuel

@[expose] noncomputable def periodK (f : Nat → Nat) (i fuel : Nat) : Nat :=
  periodGoK f i fuel i (nat_lit 0)

@[expose] noncomputable def witT (l : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) l, Nat.beq (Nat.mod l (nat_lit 3)) (nat_lit 0))

@[expose] noncomputable def pairWitK (n w fuel u y wc p : Nat) : Bool :=
  bAnd(Nat.blt p n, witT (periodK (wordK w (mask w) u y wc) p fuel))

@[expose] noncomputable def selfWitK (n w fuel y p : Nat) : Bool :=
  bAnd(Nat.blt p n, witT (periodK (pg w (mask w) y) p fuel))

@[expose] noncomputable def uFlagK (n w X X2 u : Nat) : Bool :=
  bAnd(!(Nat.beq u (pidn n w)), bAnd(Nat.beq (pw n w u (nat_lit 3)) (pidn n w),
    bAnd(!(Nat.beq u X), !(Nat.beq u X2))))

@[expose] noncomputable def yFlagK (n w fuel y p : Nat) : Bool :=
  bAnd(!(Nat.beq y (pidn n w)), !(selfWitK n w fuel y p))

@[expose] noncomputable def rankAt (f : Nat → Bool) (I R : Nat → Nat) (i : Nat) : Bool :=
  bIf(f i, bAnd(Nat.beq (I (R i)) i, Nat.beq (R (Nat.succ i)) (Nat.succ (R i))),
    Nat.beq (R (Nat.succ i)) (R i))

@[expose] noncomputable def rankEnds (N : Nat) (R : Nat → Nat) (c : Nat) : Bool :=
  bAnd(Nat.beq (R (nat_lit 0)) (nat_lit 0), Nat.beq (R N) c)

@[expose] noncomputable def wget (w : Nat) (WF : Nat → Nat) (k : Nat) : Nat :=
  pg w (mask w) (WF (Nat.div k (nat_lit 216))) (Nat.mod k (nat_lit 216))

@[expose] noncomputable def pairsK (n w fuel : Nat) (T UI YI PW : Nat → Nat) (ny a : Nat) :
    Bool :=
  allN ny fun b => strictB (PW (Nat.add (Nat.mul a ny) b)) fun v =>
    pairWitK n w fuel (T (UI a)) (T (YI b)) (Nat.mod v (nat_lit 4)) (Nat.div v (nat_lit 4))

end CFSG.KC.D4Local

end
