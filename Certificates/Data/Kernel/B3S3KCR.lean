module

public import Certificates.Data.Kernel.B3S3K

public section

namespace CFSG.KC.B3S3K

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def convCR (n w N : Nat) (T : Nat → Nat) (qs rs : List Nat)
    (WJ WR CR CG : Nat → Nat) (i : Nat) : Bool :=
  Nat.blt (CR i) N && Nat.beq (CR (CR i)) (CR i) &&
    (!(Nat.beq (CR i) i) || convAt n w N T qs rs WJ WR i) &&
    (Nat.beq (CR i) i ||
      (Nat.blt (CG i) N && Nat.blt (WJ i) N && Nat.blt (WJ (CR i)) N &&
        Nat.beq (cm n w (T i) (T (CG i))) (cm n w (T (CG i)) (T (CR i))) &&
        Nat.beq (cm n w (T (WJ i)) (T (CG i))) (cm n w (T (CG i)) (T (WJ (CR i))))))

end CFSG.KC.B3S3K

end
