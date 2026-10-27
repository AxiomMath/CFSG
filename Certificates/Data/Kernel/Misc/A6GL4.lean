module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import Certificates.Data.Kernel.Misc.GL4Lat
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.A6GL4

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4

@[expose] noncomputable def relB (x y : Nat) : Bool :=
  andB (Nat.beq (pow4F x (nat_lit 3)) id4) (andB (Nat.beq (pow4F y (nat_lit 5)) id4)
    (andB (Nat.beq (pow4F (mul4F (mul4F (mul4F x (pow4F y (nat_lit 4))) (pow4F x (nat_lit 2))) y)
      (nat_lit 2)) id4)
    (andB (Nat.beq (pow4F (mul4F (pow4F x (nat_lit 2)) (pow4F y (nat_lit 4))) (nat_lit 4)) id4)
    (andB (Nat.beq (pow4F (mul4F (mul4F (mul4F x y) x) (pow4F y (nat_lit 4))) (nat_lit 3)) id4)
      (Nat.beq (pow4F (mul4F (mul4F (mul4F (mul4F y (pow4F x (nat_lit 2))) (pow4F y (nat_lit 4)))
        (pow4F x (nat_lit 2))) y) (nat_lit 3)) id4)))))

@[expose] noncomputable def yWit (EA EAI : Nat → Nat) (Y y r : Nat) : Bool :=
  letB (fld r (nat_lit 0) (nat_lit 15)) fun w =>
    andB (Nat.blt w (nat_lit 20160)) (Nat.beq (mul4F (mul4F (EAI w) y) (EA w)) Y)

@[expose] noncomputable def yAt (EA EAI W : Nat → Nat) (Y k : Nat) : Bool :=
  letB (EA k) fun y =>
    orB (Nat.beq y id4) (orB (notB (Nat.beq (pow4F y (nat_lit 5)) id4)) (yWit EA EAI Y y (W k)))

@[expose] noncomputable def xWit (EA EAI HE : Nat → Nat) (Y x r : Nat) : Bool :=
  letB (fld r (nat_lit 15) (nat_lit 15)) fun c => letB (fld r (nat_lit 30) (nat_lit 9)) fun i =>
    letB (fld r (nat_lit 39) (nat_lit 9)) fun j =>
      andB (Nat.blt c (nat_lit 20160)) (andB (Nat.blt i (nat_lit 360)) (andB (Nat.blt j (nat_lit 360))
        (andB (Nat.beq (mul4F (mul4F (EAI c) x) (EA c)) (HE i))
          (Nat.beq (mul4F (mul4F (EAI c) Y) (EA c)) (HE j)))))

@[expose] noncomputable def xAt (EA EAI W HE : Nat → Nat) (Y k : Nat) : Bool :=
  letB (EA k) fun x =>
    orB (Nat.beq x id4) (orB (notB (Nat.beq (pow4F x (nat_lit 3)) id4))
      (orB (notB (relB x Y)) (xWit EA EAI HE Y x (W k))))

@[expose] noncomputable def djAt (HE HS R : Nat → Nat) (X Y k l : Nat) : Bool :=
  letB (mul4F (R (Nat.succ (Nat.mul (nat_lit 2) l))) (R (Nat.mul (nat_lit 2) k))) fun m =>
    letB (mul4F (R (Nat.succ (Nat.mul (nat_lit 2) k))) (R (Nat.mul (nat_lit 2) l))) fun mi =>
      orB (outK HE HS (nat_lit 360) (mul4F (mul4F m X) mi))
        (outK HE HS (nat_lit 360) (mul4F (mul4F m Y) mi))

@[expose] noncomputable def djB (HE HS R : Nat → Nat) (X Y n : Nat) : Bool :=
  andB (allN n fun k => invW (R (Nat.mul (nat_lit 2) k)) (R (Nat.succ (Nat.mul (nat_lit 2) k))))
    (allN n fun l => allN l fun k => djAt HE HS R X Y k l)

end CFSG.KC.Misc.A6GL4

end
