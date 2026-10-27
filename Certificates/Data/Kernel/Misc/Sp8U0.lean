module

public import Certificates.Data.Kernel.Misc.BfsKW
public import Certificates.Data.Kernel.Misc.Sp8Cz

public section

namespace CFSG.KD.Sp8U0

open CFSG.KD.BfsK CFSG.KD.BfsKW CFSG.KD.Sp8Syl3 CFSG.KD.Sp8Cz CFSG.KC.Mat8P CFSG.KC.Loop

@[expose] noncomputable def u0TabK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (recX R 9 0) oneP && tableKW R (rst R) 9 n 5 1024 5120 1024

@[expose] noncomputable def commG (R : Nat → Nat) (x : Nat) : Bool :=
  commN x (R 0) && (commN x (R 1) && (commN x (R 2) && (commN x (R 3) && commN x (R 4))))

@[expose] noncomputable def zuK (R : Nat → Nat) : Bool :=
  allBelow 65536 1024 fun t =>
    !(commG R (recX R 9 t)) || memN (recX R 9 t) [R 5, R 6, R 7, R 8]

end CFSG.KD.Sp8U0

end
