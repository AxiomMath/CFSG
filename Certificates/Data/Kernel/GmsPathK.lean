module

public import Certificates.Data.Kernel.VecK
public import CFSG.Certificates.Kernel.Co1M.OrbitMem

public section

namespace CFSG.KC.GmsPath

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1M

@[expose] noncomputable def xorB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b (notB b) a

@[expose] noncomputable def beqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def parF (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => xorB (bit x k) acc) (nat_lit 24)

@[expose] noncomputable def qK (Q v : Nat) : Bool := parF (Nat.land (vmF (nat_lit 24) Q v) v)

@[expose] noncomputable def polQ (Q a b : Nat) : Bool :=
  xorB (parF (Nat.land (vmF (nat_lit 24) Q a) b)) (parF (Nat.land (vmF (nat_lit 24) Q b) a))

@[expose] noncomputable def hd (z : Nat) : Bool := Nat.beq (Nat.mod z (nat_lit 4)) (nat_lit 3)

@[expose] noncomputable def hypR (m z : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih z => xorB (hd z) (ih (Nat.div z (nat_lit 4)))) m z

@[expose] noncomputable def polH (m a b : Nat) : Bool :=
  xorB (hypR m (Nat.xor a b)) (xorB (hypR m a) (hypR m b))

@[expose] noncomputable def inKb (p : Nat) : Bool :=
  orB (Nat.beq p (nat_lit 0)) (orB (Nat.beq p (nat_lit 2)) (orB (Nat.beq p (nat_lit 4)) (Nat.beq p (nat_lit 6))))

@[expose] noncomputable def cntBC (m : Nat) (b c : Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Nat.add m m) m c) m b

@[expose] noncomputable def cnt3 (a b c : Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (cntBC (nat_lit 2) b c) (cntBC (nat_lit 1) b c) a

@[expose] noncomputable def filtK (Q MX MY p : Nat) : Bool :=
  andB (Nat.blt p (pw2 (nat_lit 24))) (andB (notB (parF (Nat.land p MX)))
    (andB (notB (parF (Nat.land p MY))) (andB (notB (inKb p)) (notB (qK Q p)))))

@[expose] noncomputable def cenAt (Q MX MY : Nat) (Sf : Nat → Nat) (n b j : Nat) : Nat :=
  strictN (Sf j) fun p => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (cnt3 (orbMemK n Sf b (Nat.xor p (nat_lit 2))) (orbMemK n Sf b (Nat.xor p (nat_lit 4)))
      (orbMemK n Sf b (Nat.xor p (nat_lit 6))))
    (filtK Q MX MY p)

@[expose] noncomputable def sumS (lo cnt : Nat) (f : Nat → Nat) : Nat :=
  sumN cnt fun i => f (Nat.add lo i)

@[expose] noncomputable def basisK (Q P PI MX MY : Nat) : Bool :=
  andB (allN (nat_lit 24) fun i =>
    andB (beqB (qK Q (vmF (nat_lit 24) P (pw2 i))) (hypR (nat_lit 12) (pw2 i)))
    (andB (allN (nat_lit 24) fun j =>
      beqB (polQ Q (vmF (nat_lit 24) P (pw2 i)) (vmF (nat_lit 24) P (pw2 j)))
        (polH (nat_lit 12) (pw2 i) (pw2 j)))
    (andB (Nat.beq (vmF (nat_lit 24) PI (vmF (nat_lit 24) P (pw2 i))) (pw2 i))
    (andB (Nat.beq (vmF (nat_lit 24) P (vmF (nat_lit 24) PI (pw2 i))) (pw2 i))
    (andB (beqB (polQ Q (pw2 i) (nat_lit 2)) (parF (Nat.land (pw2 i) MX)))
      (beqB (polQ Q (pw2 i) (nat_lit 4)) (parF (Nat.land (pw2 i) MY))))))))
  (andB (Nat.beq (vmF (nat_lit 24) P (nat_lit 1)) (nat_lit 2))
  (andB (Nat.beq (vmF (nat_lit 24) P (nat_lit 4)) (nat_lit 4))
  (andB (notB (qK Q (nat_lit 2))) (andB (notB (qK Q (nat_lit 4))) (notB (qK Q (nat_lit 6)))))))

end CFSG.KC.GmsPath

end
