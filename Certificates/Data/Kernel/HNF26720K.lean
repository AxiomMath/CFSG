module

public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.HNF26720

open CFSG.KC.Ord

@[expose] noncomputable def ltr (A B Bi : Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => nIf(Nat.beq n 1, A, B))
    (fun n => nIf(Nat.beq n 0, A, Bi)) l

@[expose] noncomputable def wgo (mul : Nat → Nat → Nat) (A B Bi : Nat) (w : List Int) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => CFSG.KC.Loop.strictN (mul acc (ltr A B Bi l)) ih) w

@[expose] noncomputable def wprod (mul : Nat → Nat → Nat) (A B Bi ONE : Nat) (w : List Int) : Nat :=
  wgo mul A B Bi w ONE

@[expose] def invW (w : List Int) : List Int := w.reverse.map (fun l => -l)

@[expose] noncomputable def subOne (L H ONE X : Nat) : Nat := redP 13 L H 5 9 (X + 4 * ONE)

@[expose] noncomputable def diagR (ONE r : Nat) : Nat :=
  Nat.land (Nat.shiftRight ONE (1729 * 0)) (2 ^ (1729 * r) - 1)

@[expose] noncomputable def rkOK (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE M P Q U V r : Nat) : Bool :=
  andB (Nat.ble r 133) (andB (vld P) (andB (vld Q) (andB (vld U) (andB (vld V)
    (andB (Nat.beq (mul (mul P M) Q) (diagR ONE r))
      (Nat.beq (mul (mul U (diagR ONE r)) V) M))))))

@[expose] noncomputable def strictB (X : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) X

@[expose] noncomputable def xw (mul : Nat → Nat → Nat) (A B Bi ONE : Nat) (w : List Int) : Nat :=
  wprod mul A B Bi ONE ((1 :: w) ++ (1 :: invW w))

@[expose] noncomputable def pairOK (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (L H ONE A B Bi : Nat) (PS QS US VS KS : Nat → Nat) (w : List Int) (k : Nat) : Bool :=
  strictB (xw mul A B Bi ONE w) fun X =>
    andB (rkOK mul vld ONE (subOne L H ONE X) (PS k) (QS k) (US k) (VS k) (KS k))
      (strictB (mul X X) fun X2 =>
        rkOK mul vld ONE (subOne L H ONE X2) (PS (k + 1)) (QS (k + 1)) (US (k + 1)) (VS (k + 1))
          (KS (k + 1)))

@[expose] noncomputable def commOK (mul : Nat → Nat → Nat) (A B Bi ONE : Nat) (w : List Int) :
    Bool :=
  Nat.beq (wprod mul A B Bi ONE (1 :: w)) (wprod mul A B Bi ONE (w ++ [1]))

end CFSG.KC.HNF26720

end
