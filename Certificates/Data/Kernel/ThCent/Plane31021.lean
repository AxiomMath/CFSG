module

public import Certificates.Data.Kernel.ThCent.List

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def eig31021 (c rm ONE : Nat) (V : Nat → Nat) (X Y C : Nat)
    (e : Nat × Nat × Nat × Nat) : Bool :=
  strictF (cubeP c rm ONE X Y C 0 e.2.1 e.2.2.1) fun W =>
    andB (neB c rm ONE W ONE) (andB (Nat.beq (powB c rm ONE W 5 (nat_lit 3)) ONE)
      (Nat.beq (mulB c rm (V e.1) W) (mulB c rm (powB c rm ONE W e.2.2.2 (nat_lit 3)) (V e.1))))

@[expose] noncomputable def conj31021 (c rm ONE : Nat) (V : Nat → Nat) (X Y C : Nat)
    (d : List Nat × Nat × Nat) (i j : Nat) : Bool :=
  strictF (wordR c rm ONE V d.1) fun M =>
    andB (Nat.beq (mulB c rm M C) (mulB c rm C M))
      (Nat.beq (mulB c rm M Y) (mulB c rm (mulB c rm (powB c rm ONE (mulB c rm
        (powB c rm ONE X i (nat_lit 3)) (powB c rm ONE Y j (nat_lit 3))) d.2.1 (nat_lit 3))
        (powB c rm ONE C d.2.2 (nat_lit 3))) M))

end CFSG.KC.ThCent

end
