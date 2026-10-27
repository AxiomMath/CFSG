module

public import CFSG.Certificates.Kernel.Co1.Data.C3_Ok
public import CFSG.Certificates.Kernel.Co1.Data.C4_Ok
public import Certificates.Kernel.Co2.Join
import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Co1.Checks.C3
import CFSG.Certificates.Kernel.Co1.Checks.C4

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceSeg

theorem C3facts : Nat.beq (runFacts CFSG.KD.C3.blk CFSG.KD.C3.selWT CFSG.KD.C3.INV CFSG.KD.C3.nC
    (nat_lit 8) (seg CFSG.KD.C3.JF (Nat.sub (CFSG.KD.C3.loF 15) (CFSG.KD.C3.loF 0))
      (CFSG.KD.C3.loF 0)) (CFSG.KD.C3.accF 0)) (CFSG.KD.C3.accF 15) = true :=
  facts_chain _ _ _ _ _ _ _ _ 15 CFSG.KD.C3.okW_all

theorem C3cover : Nat.beq (runCover CFSG.KD.C3.blk CFSG.KD.C3.LVs (nat_lit 17920) (nat_lit 8)
    (seg CFSG.KD.C3.JV (Nat.sub (CFSG.KD.C3.loC 5) (CFSG.KD.C3.loC 0)) (CFSG.KD.C3.loC 0))
    (CFSG.KD.C3.accC 0)) (CFSG.KD.C3.accC 5) = true :=
  cover_chain _ _ _ _ _ _ _ 5 CFSG.KD.C3.okC_all

theorem C4facts : Nat.beq (runFacts CFSG.KD.C4.blk CFSG.KD.C4.selWT CFSG.KD.C4.INV CFSG.KD.C4.nC
    (nat_lit 6) (seg CFSG.KD.C4.JF (Nat.sub (CFSG.KD.C4.loF 1) (CFSG.KD.C4.loF 0))
      (CFSG.KD.C4.loF 0)) (CFSG.KD.C4.accF 0)) (CFSG.KD.C4.accF 1) = true :=
  facts_chain _ _ _ _ _ _ _ _ 1 CFSG.KD.C4.okW_all

theorem C4cover : Nat.beq (runCover CFSG.KD.C4.blk CFSG.KD.C4.LVs (nat_lit 216) (nat_lit 6)
    (seg CFSG.KD.C4.JV (Nat.sub (CFSG.KD.C4.loC 1) (CFSG.KD.C4.loC 0)) (CFSG.KD.C4.loC 0))
    (CFSG.KD.C4.accC 0)) (CFSG.KD.C4.accC 1) = true :=
  cover_chain _ _ _ _ _ _ _ 1 CFSG.KD.C4.okC_all

end CertificateChecks.KernelCo1

end
