module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.A6Ord

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def powFrom (b d : Nat) (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih p => orB (Nat.beq p d) (ih (mul (nat_lit 10) p b))) n

@[expose] noncomputable def pow8 (b d : Nat) : Bool := powFrom b d (nat_lit 8) (one (nat_lit 10))

@[expose] noncomputable def centB (b d : Nat) : Bool :=
  orB (notB (Nat.beq (img d (img b (nat_lit 0))) (img b (img d (nat_lit 0)))))
    (orB (notB (Nat.beq (mul (nat_lit 10) d b) (mul (nat_lit 10) b d))) (pow8 b d))

@[expose] noncomputable def ord26081 (L : List Nat) (b : Nat) : Bool :=
  letB (mul (nat_lit 10) b b) fun b2 => letB (mul (nat_lit 10) b2 b2) fun b4 =>
    letB (mul (nat_lit 10) b4 b4) fun b8 =>
      andB (orB (notB (Nat.beq (mul (nat_lit 10) b8 b8) (one (nat_lit 10))))
          (Nat.beq b8 (one (nat_lit 10))))
        (orB (notB (Nat.beq b8 (one (nat_lit 10))))
          (orB (Nat.beq b4 (one (nat_lit 10))) (allL L fun d => centB b d)))

@[expose] noncomputable def chk26081 (L : List Nat) : Bool := allL L fun b => ord26081 L b

end CFSG.KC.A6Ord
