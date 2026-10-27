module

public import Certificates.Data.Kernel.Misc.PermGH23

public section

namespace CFSG.KC.Misc.A6Aut

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GH23

@[expose] noncomputable def xC : Nat := nat_lit 16434369

@[expose] noncomputable def yC : Nat := nat_lit 16354065

@[expose] noncomputable def genC (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) yC xC (Nat.beq j 0)

@[expose] noncomputable def pow5 (a : Nat) : Nat := mul8 a (mul8 a (mul8 a (mul8 a a)))

@[expose] noncomputable def pathK (PA : Nat → Nat) (u v : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => one8)
    (fun _ ih k => Bool.rec (motive := fun _ => Nat)
      (mul8 (ih (Nat.land (PA k) (nat_lit 16777215)))
        (Bool.rec (motive := fun _ => Nat) v u (Nat.beq (Nat.shiftRight (PA k) (nat_lit 24)) 0)))
      one8 (Nat.beq k 0)) fuel

@[expose] noncomputable def fld (w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (Nat.add 1 (Nat.mul (nat_lit 9) i))) (nat_lit 511)

@[expose] noncomputable def ordOK (sq : Bool) (t : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (notB (Nat.beq t one8)) (Nat.beq (mul8 t t) one8))
    (letB (mul8 t t) fun s => andB (notB (Nat.beq s one8)) (Nat.beq (mul8 s s) one8)) sq

@[expose] noncomputable def sylOK (a b ta tb : Nat) : Bool :=
  andB (Nat.beq (mul8 (mul8 a a) a) one8) (andB (Nat.beq (mul8 (mul8 b b) b) one8)
    (andB (notB (Nat.beq a one8)) (andB (Nat.beq (mul8 a b) (mul8 b a))
      (andB (notB (Nat.beq b one8)) (andB (notB (Nat.beq b a)) (andB (notB (Nat.beq b (mul8 a a)))
        (orB (andB (Nat.beq ta (mul8 a a)) (Nat.beq tb b)) (andB (Nat.beq ta b) (Nat.beq tb a)))))))))

@[expose] noncomputable def witOK (N : Nat) (E PA : Nat → Nat) (u v w : Nat) : Bool :=
  letB (fld w 0) fun ig => letB (fld w 1) fun ih =>
    andB (Nat.blt ig N) (andB (Nat.blt ih N) (andB (Nat.beq (mul8 (E ig) (E ih)) one8)
      (andB (ordOK (Nat.beq (Nat.land w 1) 0) (mul8 (pathK PA u v N ig) (E ih)))
        (Bool.rec (motive := fun _ => Bool)
          (letB (fld w 2) fun ia => letB (fld w 3) fun ib =>
            andB (Nat.blt ia N) (andB (Nat.blt ib N)
              (sylOK (E ia) (E ib) (pathK PA u v N ia) (pathK PA u v N ib))))
          true (Nat.beq (Nat.land w 1) 0)))))

@[expose] noncomputable def pairOK (N : Nat) (E PA : Nat → Nat) (iu iv w : Nat) : Bool :=
  letB (E iu) fun u => letB (E iv) fun v =>
    impB (andB (Nat.beq (pow5 (mul8 u v)) one8) (Nat.beq (pow5 (mul8 u (mul8 v v))) one8))
      (impB (andB (Nat.beq (pathK PA u v N iu) xC) (Nat.beq (pathK PA u v N iv) yC))
        (orB (andB (Nat.beq u xC) (Nat.beq v yC)) (witOK N E PA u v w)))

@[expose] noncomputable def rowAt (N : Nat) (E PA L2 L4 W : Nat → Nat) (n4 r : Nat) : Bool :=
  allN n4 fun c => pairOK N E PA (L2 r) (L4 c) (W (Nat.add (Nat.mul n4 r) c))

@[expose] noncomputable def rec2At (E L2 R2 : Nat → Nat) (n2 k : Nat) : Bool :=
  impB (Nat.beq (mul8 (E k) (E k)) one8)
    (letB (R2 k) fun r => andB (Nat.blt r n2) (Nat.beq (L2 r) k))

@[expose] noncomputable def rec4At (E L4 R4 : Nat → Nat) (n4 k : Nat) : Bool :=
  impB (letB (mul8 (E k) (E k)) fun s => Nat.beq (mul8 s s) one8)
    (letB (R4 k) fun r => andB (Nat.blt r n4) (Nat.beq (L4 r) k))

end CFSG.KC.Misc.A6Aut

end
