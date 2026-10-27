module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def rowsBind (n w : Nat) (P : Nat → Nat) (rows : List (List Nat))
    (k : Nat) : Bool :=
  (rows.zipIdx k).all fun p =>
    Nat.beq p.1.length n && (packL w p.1).2 && Nat.beq (packL w p.1).1 (P p.2)

end CFSG.KC.Misc.ArrEnum

end
