module

public import Certificates.Data.Kernel.Tower.Tree

public section

namespace Certificates.KernelTower

@[expose] noncomputable def tm (mul : Nat → Nat → Nat) (FA g a b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.add (Nat.mul 2 (mul (Nat.shiftRight a 1) (Nat.shiftRight b 1))) (Nat.land b 1))
    (Bool.rec (motive := fun _ => Nat)
      (Nat.add (Nat.mul 2 (mul (Nat.shiftRight a 1) (l16 FA (Nat.shiftRight b 1)))) 1)
      (Nat.mul 2 (mul (mul (Nat.shiftRight a 1) (l16 FA (Nat.shiftRight b 1))) g))
      (Nat.beq (Nat.land b 1) 1))
    (Nat.beq (Nat.land a 1) 1)

@[expose] noncomputable def eqB (b c : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false c) c b

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] def bitS (S k : Nat) : Bool := Nat.blt 0 (Nat.land S (Nat.shiftLeft 1 k))

@[expose] def bitN (S k : Nat) : Nat := Nat.land (Nat.shiftRight S k) 1

@[expose] def par64 : Nat := 7608434000728254870

@[expose] def chiT (T k : Nat) : Nat :=
  Nat.xor (Nat.xor (bitN par64 (Nat.land (Nat.land (Nat.shiftRight k 1) 63)
      (Nat.land (Nat.shiftRight T 128) 63))) (bitN T (Nat.shiftRight k 7)))
    (Nat.land k (bitN T 134))

@[expose] def xbit (T k : Nat) : Nat := Nat.land (chiT T k) 1

@[expose] noncomputable def famK (H S X : Nat → Nat) (U HM k p : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (notB (bitS U k))
    (allB 16 fun j => eqB (bitS (S j) k)
      (Nat.beq (Nat.xor p (Nat.mul 2 (xbit (X j) k))) (H j)))
    (bitS HM p)

@[expose] noncomputable def famC (mul2 : Nat → Nat → Nat) (PT IMW FTW b : Nat) (H S X : Nat → Nat)
    (U HM c f : Nat) : Bool :=
  (Nat.beq c 0 || Nat.beq f (mul2 (l16 IMW (ptGi PT c)) (l16 FTW (ptPar PT c)))) &&
    famK H S X U HM (Nat.mul 2 c) (mul2 (Nat.mul 2 c) f) &&
      famK H S X U HM (Nat.add (Nat.mul 2 c) 1) (mul2 (Nat.add (Nat.mul 2 c) 1) (mul2 f b))

@[expose] noncomputable def famB (mul2 : Nat → Nat → Nat) (PT IMW FTW b : Nat)
    (H S X : Nat → Nat) (U HM : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 IMW i) 16384) && Nat.blt b 16384 && Nat.beq (l16 FTW 0) 0 &&
    allB 16 (fun j => Nat.blt (H j) 16384 && bitS HM (H j) && bitS HM (Nat.xor (H j) 2)) &&
      allB 8192 fun c => famC mul2 PT IMW FTW b H S X U HM c (l16 FTW c)

end Certificates.KernelTower
