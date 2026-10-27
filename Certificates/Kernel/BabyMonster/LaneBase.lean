module

public import CFSG.Certificates.Kernel.BabyMonster.DyLaneUse
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Bind
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Check0
public import Certificates.Kernel.BabyMonster.ForallLt
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.PktTab
public import CFSG.Certificates.Kernel.BabyMonster.Sound

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Ln

theorem blocks : blocksOK CFSG.KC.BM.Dyadic.Bs = true := by quickRfl

theorem rows : ∀ j < 4371, dyRowOK 4371 j (recOf CFSG.KC.BM.Dyadic.Bs j) = true :=
  dyBasisOK_sound blocks CFSG.KC.BM.Dyadic.basis

theorem lnData : LnData CFSG.KC.BM.Dyadic.Bs CFSG.KC.BM.Dyadic.SS CFSG.KC.BM.Dyadic.KK :=
  ⟨blocks, rows, by forall_lt_consts CFSG.KC.BM.Dyadic.lnStrip 274,
    by rw [← dyLenLL_eq]; exact Nat.eq_of_beq_eq_true CFSG.KC.BM.Dyadic.lnSSLen,
    lnEqLL_sound CFSG.KC.BM.Dyadic.lnKKOK⟩

end CertificateChecks.KernelBM.Dy

end
