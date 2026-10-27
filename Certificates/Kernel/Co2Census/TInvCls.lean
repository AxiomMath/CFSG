module

public import Certificates.Kernel.Co2Cls.DS
public import Certificates.Kernel.Co2Cls.D4
public import Certificates.Kernel.Co2Cls.D5
public import Certificates.Kernel.Co2Cls.D6
public import Certificates.Kernel.Co2Cls.D9

public section

namespace CertificateChecks.KernelSpor.Co2TInv

open CFSG.KC.Co2InvS CertificateChecks.KernelSpor.Co2Cls

@[expose] noncomputable def CFS (c k : Nat) : Nat :=
  selN (Nat.beq c 0) (C0 k) (selN (Nat.beq c 1) (C1 k) (selN (Nat.beq c 2) (C2 k)
    (selN (Nat.beq c 3) (C3 k) (selN (Nat.beq c 4) (C4 k) (selN (Nat.beq c 5) (C5 k)
    (selN (Nat.beq c 6) (C6 k) (selN (Nat.beq c 7) (C7 k) (selN (Nat.beq c 8) (C8 k)
    (selN (Nat.beq c 9) (C9 k) 0)))))))))

@[expose] noncomputable def NCS (c : Nat) : Nat :=
  selN (Nat.beq c 0) 1 (selN (Nat.beq c 1) 270 (selN (Nat.beq c 2) 1260
    (selN (Nat.beq c 3) 1260 (selN (Nat.beq c 4) 22680 (selN (Nat.beq c 5) 15120
    (selN (Nat.beq c 6) 15120 (selN (Nat.beq c 7) 1008 (selN (Nat.beq c 8) 1008
    (selN (Nat.beq c 9) 120960 0)))))))))

end CertificateChecks.KernelSpor.Co2TInv

end
