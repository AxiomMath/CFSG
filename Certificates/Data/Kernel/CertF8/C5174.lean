module

public import Certificates.Data.Kernel.CertF8.G9557

public section

namespace CFSG.KC.CertF8.G9557

@[expose] def cen5174K (a b c : Nat) : Bool :=
  (List.range 243).all fun n =>
    !(Nat.beq (pm n 27) (pm 27 n) && Nat.beq (pm n 3) (pm 3 n) && Nat.beq (pm n 1) (pm 1 n)) ||
      Nat.beq n a || Nat.beq n b || Nat.beq n c

end CFSG.KC.CertF8.G9557

end
