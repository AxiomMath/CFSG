module

public import Certificates.Data.Kernel.O8.Core

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def bb (x y i j : Nat) : Nat := Nat.land (bitN x i) (bitN y j)

@[expose] noncomputable def q8K (e : Bool) (v : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.xor (Nat.xor (bb v v 0 4) (bb v v 1 5)) (Nat.xor (bb v v 2 6) (bb v v 3 7)))
    (Nat.xor (Nat.xor (bb v v 0 3) (bb v v 1 4)) (Nat.xor (bb v v 2 5)
      (Nat.xor (bitN v 6) (Nat.xor (bb v v 6 7) (bitN v 7))))) e

@[expose] noncomputable def b8K (e : Bool) (v w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.xor (Nat.xor (Nat.xor (bb v w 0 4) (bb w v 0 4)) (Nat.xor (bb v w 1 5) (bb w v 1 5)))
      (Nat.xor (Nat.xor (bb v w 2 6) (bb w v 2 6)) (Nat.xor (bb v w 3 7) (bb w v 3 7))))
    (Nat.xor (Nat.xor (Nat.xor (bb v w 0 3) (bb w v 0 3)) (Nat.xor (bb v w 1 4) (bb w v 1 4)))
      (Nat.xor (Nat.xor (bb v w 2 5) (bb w v 2 5)) (Nat.xor (bb v w 6 7) (bb w v 6 7)))) e

@[expose] noncomputable def eichK (e : Bool) (u w x : Nat) : Nat :=
  Nat.xor (Nat.xor x (Nat.mul (b8K e x u) w))
    (Nat.xor (Nat.mul (b8K e x w) u) (Nat.mul (Nat.land (q8K e w) (b8K e x u)) u))

@[expose] noncomputable def transK (e : Bool) (v x : Nat) : Nat := Nat.xor x (Nat.mul (b8K e x v) v)

@[expose] noncomputable def nsOK (e : Bool) (N NS NI : Nat) : Bool :=
  andB (allN N fun j => (fun v => andB (Nat.blt v (nat_lit 256)) (andB (Nat.beq (q8K e v) (nat_lit 1))
      (andB (Nat.beq (fget NI v (nat_lit 8)) j)
        (orB (Nat.beq j (nat_lit 0)) (Nat.blt (fget NS (Nat.sub j (nat_lit 1)) (nat_lit 8)) v)))))
      (fget NS j (nat_lit 8)))
    (allN (nat_lit 256) fun v => (fun i => Bool.rec (motive := fun _ => Bool) (Nat.beq i N)
        (andB (Nat.blt i N) (Nat.beq (fget NS i (nat_lit 8)) v)) (Nat.beq (q8K e v) (nat_lit 1)))
      (fget NI v (nat_lit 8)))

@[expose] noncomputable def nsMap (NS NI : Nat) (f : Nat → Nat) (j : Nat) : Nat :=
  fget NI (f (fget NS j (nat_lit 8))) (nat_lit 8)

@[expose] noncomputable def rootPK (NS NI u0 w0 u1 w1 u2 w2 : Nat) : Nat :=
  orN (nat_lit 360) fun i => (fun k j => Nat.shiftLeft
      (Nat.add (Nat.mul (nat_lit 120) k)
        (nsMap NS NI (eichK false (nIf(Nat.beq k (nat_lit 0), u0, nIf(Nat.beq k (nat_lit 1), u1, u2)))
          (nIf(Nat.beq k (nat_lit 0), w0, nIf(Nat.beq k (nat_lit 1), w1, w2)))) j))
      (Nat.mul (nat_lit 9) i))
    (Nat.div i (nat_lit 120)) (Nat.mod i (nat_lit 120))

@[expose] noncomputable def rhoPK : Nat :=
  orN (nat_lit 360) fun i => Nat.shiftLeft (Nat.mod (Nat.add i (nat_lit 120)) (nat_lit 360)) (Nat.mul (nat_lit 9) i)

@[expose] noncomputable def tauPK (NS NI : Nat) : Nat :=
  orN (nat_lit 360) fun i => Nat.shiftLeft
    (Nat.add (Nat.mul (nat_lit 120) (Nat.mod (Nat.sub (nat_lit 3) (Nat.div i (nat_lit 120))) (nat_lit 3)))
      (nsMap NS NI (transK false (nat_lit 136)) (Nat.mod i (nat_lit 120))))
    (Nat.mul (nat_lit 9) i)

@[expose] noncomputable def eichMK (NS NI u w : Nat) : Nat :=
  orN (nat_lit 136) fun i => Nat.shiftLeft (nsMap NS NI (eichK true u w) i) (Nat.mul (nat_lit 8) i)

@[expose] noncomputable def transMK (NS NI : Nat) : Nat :=
  orN (nat_lit 136) fun i => Nat.shiftLeft (nsMap NS NI (transK true (nat_lit 64)) i) (Nat.mul (nat_lit 8) i)

@[expose] noncomputable def RP : Nat :=
  nat_lit 2463978225790262102547757167728541113913435905619858500132119053786699876193843091108650615906224537599028532355073

@[expose] noncomputable def GP : Nat := nat_lit 1096851013191405815183777867003602740157589098497

@[expose] noncomputable def genP (NS NI j : Nat) : Nat :=
  (fun f => nIf(Nat.blt j (nat_lit 8),
      rootPK NS NI (f (nat_lit 0)) (f (nat_lit 1)) (f (nat_lit 2)) (f (nat_lit 3)) (f (nat_lit 4)) (f (nat_lit 5)),
      nIf(Nat.beq j (nat_lit 8), rhoPK, tauPK NS NI)))
    (fun t => fget RP (Nat.add (Nat.mul (nat_lit 6) j) t) (nat_lit 8))

@[expose] noncomputable def genM (NS NI j : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 10),
    eichMK NS NI (fget GP (Nat.mul (nat_lit 2) j) (nat_lit 8)) (fget GP (Nat.succ (Nat.mul (nat_lit 2) j)) (nat_lit 8)),
    transMK NS NI)

@[expose] noncomputable def fromWK (bp y : Nat) : Nat :=
  orN (nat_lit 6) fun j => Nat.shiftLeft (bitN y j) (fget bp j (nat_lit 4))

@[expose] noncomputable def psiK (e : Bool) (NS NI N w bp y : Nat) : Nat :=
  strictN (fromWK bp y) fun v =>
    orN N fun i => Nat.shiftLeft (nsMap NS NI (eichK e (nat_lit 1) v) i) (Nat.mul w i)

end CFSG.KC.O8

end
