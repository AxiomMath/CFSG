module

public import Certificates.Data.Kernel.KDense.Bind

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def f12 (T i : Nat) : Nat := fld(T, Nat.mul (nat_lit 12) i, nat_lit 4095)

@[expose] noncomputable def thOK (TH : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun a ih => andB (Nat.beq (f12 TH a) (thetaT a)) ih) (nat_lit 4096)

@[expose] noncomputable def octOK (OCT : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun ok n => andB ok (Nat.beq n (nat_lit 759)))
    (Nat.rec (motive := fun _ => Bool × Nat) (true, nat_lit 0)
      (fun a ih => Prod.rec (motive := fun _ => Bool × Nat) (fun ok n =>
        Bool.rec (motive := fun _ => Bool × Nat) (ok, n) (andB ok (Nat.beq (f12 OCT n) a), Nat.add n (nat_lit 1))
          (Nat.beq (popc24 (wordT a)) (nat_lit 8))) ih) (nat_lit 4096))

@[expose] noncomputable def du1OK (DU1 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (Nat.beq (f12 DU1 i) (dualT (Nat.shiftLeft (nat_lit 1) i))) ih) (nat_lit 24)

@[expose] noncomputable def dualL (DU1 v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (selB (bitN v i) (f12 DU1 i))) (nat_lit 24)

@[expose] noncomputable def spreadT (w m : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun acc _ => acc)
    (Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0)
      (fun k ih => Prod.rec (motive := fun _ => Nat × Nat) (fun acc t =>
        Bool.rec (motive := fun _ => Nat × Nat) (acc, t)
          (Nat.lor acc (Nat.shiftLeft (bitN m t) k), Nat.add t (nat_lit 1)) (Nat.beq (bitN w k) (nat_lit 1))) ih)
      (nat_lit 24))

@[expose] noncomputable def oddCodeT (c i : Nat) : Nat :=
  Nat.xor c (selB (Nat.xor (bitN (wordT c) i) (pT c)) (nat_lit 63))

@[expose] noncomputable def octCodeT (a m : Nat) : Nat :=
  Nat.xor a (selB (Nat.land (Nat.shiftRight (popc24 (spreadT (wordT a) m)) (nat_lit 1)) (nat_lit 1)) (nat_lit 63))

@[expose] noncomputable def keyRec (a d : Nat) : Nat := Nat.lor a (Nat.shiftLeft d (nat_lit 12))

@[expose] noncomputable def keyAtPos (TH OCT DU1 p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      ((fun pp => (fun i j => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (keyRec (selB (bitN pp (nat_lit 10)) (nat_lit 63))
            (dualT (Nat.lor (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j))))
          (andB (Nat.blt pp (nat_lit 2048)) (andB (Nat.blt i j) (Nat.blt j (nat_lit 24)))))
          (Nat.land (Nat.shiftRight pp (nat_lit 5)) (nat_lit 31)) (Nat.land pp (nat_lit 31)))
        (Nat.sub p (nat_lit 114688)))
      ((fun q => (fun a0 mq => (fun b => keyRec b (Nat.xor (f12 TH b) (dualL DU1 (spreadT (wordT a0) mq))))
          (octCodeT a0 mq))
        (f12 OCT (Nat.shiftRight q (nat_lit 6)))
        ((fun r => Nat.add (Nat.shiftLeft r (nat_lit 1)) (parT (nat_lit 6) r)) (Nat.land q (nat_lit 63))))
        (Nat.sub p (nat_lit 65536)))
      (Nat.blt p (nat_lit 114112)))
    ((fun t i => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        ((fun a => keyRec a (Nat.xor (f12 TH a) (f12 DU1 i))) (oddCodeT (Nat.shiftLeft t (nat_lit 1)) i))
        (Nat.blt i (nat_lit 24)))
      (Nat.shiftRight p (nat_lit 5)) (Nat.land p (nat_lit 31)))
    (Nat.blt p (nat_lit 65536))

@[expose] noncomputable def keyRange (TH OCT DU1 : Nat) (d : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun K lo => Nat.beq K (keyAtPos TH OCT DU1 lo))
    (fun e ih K lo => (fun h => andB (ih (Nat.land K (ones (Nat.mul (nat_lit 32) h))) lo)
        (ih (Nat.shiftRight K (Nat.mul (nat_lit 32) h)) (Nat.add lo h)))
      (Nat.shiftLeft (nat_lit 1) e)) d

@[expose] noncomputable def keySlice (KT i : Nat) : Nat :=
  Nat.land (Nat.shiftRight KT (Nat.mul i (nat_lit 524288))) (ones (nat_lit 524288))

@[expose] noncomputable def keysOK (TH OCT DU1 KT : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (keyRange TH OCT DU1 (nat_lit 14) (keySlice KT i) (Nat.mul i (nat_lit 16384))) ih) (nat_lit 8)

@[expose] noncomputable def keyPlanesOK (F : Fix) (KT : Nat) : Bool :=
  andB
    (Nat.beq F.keyA (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b acc => Nat.lor acc (Nat.shiftLeft (rawPlane KT (nat_lit 32) SX (nat_lit 17) (nat_lit 0) b) (Nat.mul b SX)))
      (nat_lit 12)))
    (Nat.beq F.keyD (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b acc => Nat.lor acc (Nat.shiftLeft (rawPlane KT (nat_lit 32) SX (nat_lit 17) (nat_lit 0)
        (Nat.add b (nat_lit 12))) (Nat.mul b SX)))
      (nat_lit 12)))

end CFSG.KC.KDense

end
