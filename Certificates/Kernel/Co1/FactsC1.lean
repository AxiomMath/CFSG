module

public import CFSG.Certificates.Kernel.Co1.Data.C1_Ok
public import Certificates.Kernel.Co2.Join
import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Co1.Checks.C1W0
import CFSG.Certificates.Kernel.Co1.Checks.C1W1
import CFSG.Certificates.Kernel.Co1.Checks.C1C

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceSeg

theorem C1facts : Nat.beq (runFacts CFSG.KD.C1.blk CFSG.KD.C1.selWT CFSG.KD.C1.INV CFSG.KD.C1.nC
    (nat_lit 16) (seg CFSG.KD.C1.JF (Nat.sub (CFSG.KD.C1.loF 481) (CFSG.KD.C1.loF 0))
      (CFSG.KD.C1.loF 0)) (CFSG.KD.C1.accF 0)) (CFSG.KD.C1.accF 481) = true :=
  facts_chain _ _ _ _ _ _ _ _ 481 (forall_append 256 225 CFSG.KD.C1.okW_0 CFSG.KD.C1.okW_1)

theorem C1cover : Nat.beq (runCover CFSG.KD.C1.blk CFSG.KD.C1.LVs (nat_lit 798663) (nat_lit 16)
    (seg CFSG.KD.C1.JV (Nat.sub (CFSG.KD.C1.loC 197) (CFSG.KD.C1.loC 0)) (CFSG.KD.C1.loC 0))
    (CFSG.KD.C1.accC 0)) (CFSG.KD.C1.accC 197) = true :=
  cover_chain _ _ _ _ _ _ _ 197 CFSG.KD.C1.okC_all

end CertificateChecks.KernelCo1

end
