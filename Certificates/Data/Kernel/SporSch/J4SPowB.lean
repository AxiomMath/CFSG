module

public import Certificates.Data.Kernel.J4Q.Mat

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def powBK (c rm one : Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => one)
    (fun _ ih M e => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (strictN (mulJ c rm M M) fun MM => strictN (ih MM (Nat.div e (nat_lit 2))) fun Y =>
          Bool.rec (motive := fun _ => Nat) Y (mulJ c rm M Y)
            (Nat.beq (Nat.mod e (nat_lit 2)) (nat_lit 1)))
        M (Nat.beq e (nat_lit 1)))
      one (Nat.beq e (nat_lit 0))) f

end CFSG.KS.SporSch.J4B

end
