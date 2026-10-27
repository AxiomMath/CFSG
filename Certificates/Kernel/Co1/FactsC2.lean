module

public import CFSG.Certificates.Kernel.Co1.Data.C2_Ok
public import Certificates.Kernel.Co2.Join
import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Co1.Checks.C2W0
import CFSG.Certificates.Kernel.Co1.Checks.C2W1
import CFSG.Certificates.Kernel.Co1.Checks.C2W2
import CFSG.Certificates.Kernel.Co1.Checks.C2C

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceSeg

theorem C2facts : Nat.beq (runFacts CFSG.KD.C2.blk CFSG.KD.C2.selWT CFSG.KD.C2.INV CFSG.KD.C2.nC
    (nat_lit 14) (seg CFSG.KD.C2.JF (Nat.sub (CFSG.KD.C2.loF 620) (CFSG.KD.C2.loF 0))
      (CFSG.KD.C2.loF 0)) (CFSG.KD.C2.accF 0)) (CFSG.KD.C2.accF 620) = true :=
  facts_chain _ _ _ _ _ _ _ _ 620
    (forall_append 512 108 (forall_append 256 256 CFSG.KD.C2.okW_0 CFSG.KD.C2.okW_1)
      CFSG.KD.C2.okW_2)

theorem C2cover : Nat.beq (runCover CFSG.KD.C2.blk CFSG.KD.C2.LVs (nat_lit 1140939) (nat_lit 14)
    (seg CFSG.KD.C2.JV (Nat.sub (CFSG.KD.C2.loC 94) (CFSG.KD.C2.loC 0)) (CFSG.KD.C2.loC 0))
    (CFSG.KD.C2.accC 0)) (CFSG.KD.C2.accC 94) = true :=
  cover_chain _ _ _ _ _ _ _ 94 CFSG.KD.C2.okC_all

end CertificateChecks.KernelCo1

end
