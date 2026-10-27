module

public import Certificates.Kernel.Co2Census.HPDefs
public import Certificates.Kernel.Co2Census.HPData
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

@[expose] noncomputable def ER (e : Nat) : Nat := mulV (SK 0) (QKt e)

theorem E_center : ∀ e < 512, (Nat.beq e 0 || Nat.beq e 256 || (List.range 8).any fun i =>
    !Nat.beq (mulV (ER e) (ER (2 ^ i))) (mulV (ER (2 ^ i)) (ER e))) = true := by
  kc_cover 64

theorem E_misc : (Nat.beq (mulV (ER 2) (ER 2)) (ER 0) && Nat.beq (mulV (ER 32) (ER 32)) (ER 0) &&
    Nat.beq (mulV (ER 2) (ER 1)) (mulV (ER 1) (ER 2)) &&
    Nat.beq (mulV (ER 32) (ER 1)) (mulV (ER 1) (ER 32)) &&
    !Nat.beq (mulV (ER 2) (ER 32)) (mulV (ER 32) (ER 2))) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
