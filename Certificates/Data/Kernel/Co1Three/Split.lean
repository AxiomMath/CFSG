module

public import Certificates.Data.Kernel.Co1Three.Leaf

public section

namespace CFSG.KC.Co1Leaf

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.KC.Co1B

@[expose] noncomputable def pairK (X Y u : Nat) : Nat :=
  mulWK (powWK X (Nat.mod u (nat_lit 3))) (powWK Y (Nat.div u (nat_lit 3)))

@[expose] noncomputable def commL (F : List Nat) (X : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun f _ ih => andB (Nat.beq (mulWK f X) (mulWK X f)) ih) F

@[expose] noncomputable def distK (X Y : Nat) : Bool :=
  allN (nat_lit 9) fun u => allN (nat_lit 9) fun v =>
    orB (Nat.beq u v) (notB (Nat.beq (Nat.mod (pairK X Y u) (pw2 (nat_lit 576)))
      (Nat.mod (pairK X Y v) (pw2 (nat_lit 576)))))

@[expose] noncomputable def planeK (F : List Nat) (X Y : Nat) : Bool :=
  andB (Nat.beq (mulWK X Y) (mulWK Y X))
    (andB (Nat.beq (mulWK X (mulWK X X)) oneK)
      (andB (Nat.beq (mulWK Y (mulWK Y Y)) oneK)
        (andB (commL F X) (andB (commL F Y) (distK X Y)))))

end CFSG.KC.Co1Leaf

end
