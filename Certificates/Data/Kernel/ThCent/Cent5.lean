module

public import Certificates.Data.Kernel.ThCent.List

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def letterOK (c rm ONE R Ri X Y C i j k i' j' k' : Nat) : Bool :=
  andB (Nat.beq (mulB c rm R Ri) ONE)
    (andB (Nat.beq (mulB c rm (mulB c rm R X) Ri) (cubeP c rm ONE X Y C i j k))
      (Nat.beq (mulB c rm (mulB c rm R Y) Ri) (cubeP c rm ONE X Y C i' j' k')))

@[expose] noncomputable def cent5OK (c rm ONE : Nat) (V : Nat → Nat) (X Y C : Nat) (w : List Nat) :
    Bool :=
  strictF (wordR c rm ONE V w) fun E =>
    Bool.or (neB c rm ONE (mulB c rm E X) (mulB c rm X E))
      (Bool.or (neB c rm ONE (mulB c rm E Y) (mulB c rm Y E))
        ((List.range 5).any fun k => Nat.beq E (powB c rm ONE C k (nat_lit 3))))

end CFSG.KC.ThCent

end
