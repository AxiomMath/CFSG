module

public import Certificates.Data.Kernel.GmsPathK
public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KC.GmsPath

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1M CFSG.KC.Co1F2

@[expose] noncomputable def l1K (Q : Nat) (O : Nat → Bool) (w : Nat) : Bool :=
  andB (notB (Nat.beq w (nat_lit 0))) (andB (notB (qK Q w)) (notB (O w)))

@[expose] noncomputable def l3K (Q : Nat) (O : Nat → Bool) (w : Nat) : Bool :=
  andB (notB (Nat.beq w (nat_lit 0))) (andB (notB (qK Q w)) (O w))

@[expose] noncomputable def pat0K (Q : Nat) (O : Nat → Bool) (v : Nat) : Bool :=
  andB (l3K Q O (Nat.xor v (nat_lit 6))) (andB (l3K Q O (Nat.xor v (nat_lit 4)))
  (andB (l1K Q O v) (andB (l3K Q O (Nat.xor v (nat_lit 2)))
  (andB (l1K Q O (Nat.xor v (nat_lit 40))) (andB (l1K Q O (Nat.xor v (nat_lit 42)))
  (andB (l1K Q O (Nat.xor v (nat_lit 44))) (l1K Q O (Nat.xor v (nat_lit 46)))))))))

@[expose] noncomputable def applyK (Ms path : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun l _ ih v => ih (vmF (nat_lit 24) (getL (nat_lit 0) Ms l) v)) path v

@[expose] noncomputable def killedK (Q : Nat) (O : Nat → Bool) (Ms path : List Nat) (v : Nat) :
    Bool :=
  strictB (Nat.xor v (applyK Ms path v)) fun w =>
    andB (Nat.blt w (pw2 (nat_lit 24))) (andB (notB (Nat.beq w (nat_lit 0))) (notB (pat0K Q O w)))

@[expose] noncomputable def witAt (Q MX MY : Nat) (Ms pA pB : List Nat) (Sf : Nat → Nat)
    (n b j : Nat) : Bool :=
  strictB (Sf j) fun p => strictB (Nat.xor p (nat_lit 2)) fun v =>
    orB (notB (andB (Nat.blt p (pw2 (nat_lit 24))) (andB (notB (parF (Nat.land p MX)))
      (notB (parF (Nat.land p MY))))))
    (orB (notB (pat0K Q (orbMemK n Sf b) v)) (orB (Nat.beq v (nat_lit 1))
      (orB (killedK Q (orbMemK n Sf b) Ms pA v) (killedK Q (orbMemK n Sf b) Ms pB v))))

@[expose] noncomputable def Xc (CM c : Nat) : Nat := vmF (nat_lit 24) CM (Nat.shiftLeft c (nat_lit 16))

@[expose] noncomputable def dualK (CM DM : Nat) (GS : List Nat) : Bool :=
  allN (nat_lit 24) fun i =>
    andB (Nat.beq (vmF (nat_lit 24) CM (vmF (nat_lit 24) DM (pw2 i))) (pw2 i))
    (andB (Nat.beq (vmF (nat_lit 24) DM (vmF (nat_lit 24) CM (pw2 i))) (pw2 i))
      (allN (nat_lit 16) fun k =>
        beqB (bit (vmF (nat_lit 24) DM (pw2 i)) k) (parF (Nat.land (pw2 i) (getL (nat_lit 0) GS k)))))

@[expose] noncomputable def maskK (Q : Nat) (O : Nat → Bool) (CM M2 M4 : Nat) : Bool :=
  allN (nat_lit 256) fun c =>
    andB (beqB (bit M2 c) (l3K Q O (Xc CM c))) (beqB (bit M4 c) (l1K Q O (Xc CM c)))

@[expose] noncomputable def shK (SH d : Nat) : Nat := fget SH d (nat_lit 256)

@[expose] noncomputable def shiftK (M4 SH : Nat) : Bool :=
  allN (nat_lit 256) fun d => allN (nat_lit 256) fun c =>
    beqB (bit (shK SH d) c) (bit M4 (Nat.xor c d))

@[expose] noncomputable def pairK (M2 M4 SH : Nat) : Bool :=
  allN (nat_lit 256) fun a => orB (notB (bit M2 a)) (allN (nat_lit 256) fun b =>
    orB (notB (bit M2 b)) (orB (notB (bit M2 (Nat.xor a b)))
      (Nat.beq (Nat.land M4 (Nat.land (shK SH a) (Nat.land (shK SH b) (shK SH (Nat.xor a b)))))
        (nat_lit 0))))

end CFSG.KC.GmsPath

end
