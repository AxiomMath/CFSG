module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Co2.Bound3.Checks.T
public import CFSG.Certificates.Kernel.Co2.Bound.Checks.P
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC.LceS CFSG.KC.LceSeg

theorem P4facts : Nat.beq (runFacts CFSG.KD.Co2KP4.blk CFSG.KD.Co2KP4.selWT CFSG.KD.Co2KP4.INV
    CFSG.KD.Co2KP4.nC (nat_lit 4) (seg CFSG.KD.Co2KP4.JF
      (Nat.sub (CFSG.KD.Co2KP4.loF 105) (CFSG.KD.Co2KP4.loF 0)) (CFSG.KD.Co2KP4.loF 0))
    (CFSG.KD.Co2KP4.accF 0)) (CFSG.KD.Co2KP4.accF 105) = true :=
  facts_chain _ _ _ _ _ _ _ _ 105 CFSG.KD.Co2KP4.okW_all

theorem P4cover : Nat.beq (runCover CFSG.KD.Co2KP4.blk CFSG.KD.Co2KP4.LVs (nat_lit 138182)
    (nat_lit 4) (seg CFSG.KD.Co2KP4.JV
      (Nat.sub (CFSG.KD.Co2KP4.loC 26) (CFSG.KD.Co2KP4.loC 0)) (CFSG.KD.Co2KP4.loC 0))
    (CFSG.KD.Co2KP4.accC 0)) (CFSG.KD.Co2KP4.accC 26) = true :=
  cover_chain _ _ _ _ _ _ _ 26 CFSG.KD.Co2KP4.okC_all

theorem X2facts : Nat.beq (runFacts CFSG.KD.Co2KX2.blk CFSG.KD.Co2KX2.selWT CFSG.KD.Co2KX2.INV
    CFSG.KD.Co2KX2.nC (nat_lit 8) (seg CFSG.KD.Co2KX2.JF
      (Nat.sub (CFSG.KD.Co2KX2.loF 40) (CFSG.KD.Co2KX2.loF 0)) (CFSG.KD.Co2KX2.loF 0))
    (CFSG.KD.Co2KX2.accF 0)) (CFSG.KD.Co2KX2.accF 40) = true :=
  facts_chain _ _ _ _ _ _ _ _ 40 CFSG.KD.Co2KX2.okW_all

theorem X2cover : Nat.beq (runCover CFSG.KD.Co2KX2.blk CFSG.KD.Co2KX2.LVs (nat_lit 81493)
    (nat_lit 8) (seg CFSG.KD.Co2KX2.JV
      (Nat.sub (CFSG.KD.Co2KX2.loC 8) (CFSG.KD.Co2KX2.loC 0)) (CFSG.KD.Co2KX2.loC 0))
    (CFSG.KD.Co2KX2.accC 0)) (CFSG.KD.Co2KX2.accC 8) = true :=
  cover_chain _ _ _ _ _ _ _ 8 CFSG.KD.Co2KX2.okC_all

theorem X3facts : Nat.beq (runFacts CFSG.KD.Co2KX3.blk CFSG.KD.Co2KX3.selWT CFSG.KD.Co2KX3.INV
    CFSG.KD.Co2KX3.nC (nat_lit 10) (seg CFSG.KD.Co2KX3.JF
      (Nat.sub (CFSG.KD.Co2KX3.loF 64) (CFSG.KD.Co2KX3.loF 0)) (CFSG.KD.Co2KX3.loF 0))
    (CFSG.KD.Co2KX3.accF 0)) (CFSG.KD.Co2KX3.accF 64) = true :=
  facts_chain _ _ _ _ _ _ _ _ 64 CFSG.KD.Co2KX3.okW_all

theorem X3cover : Nat.beq (runCover CFSG.KD.Co2KX3.blk CFSG.KD.Co2KX3.LVs (nat_lit 139657)
    (nat_lit 10) (seg CFSG.KD.Co2KX3.JV
      (Nat.sub (CFSG.KD.Co2KX3.loC 7) (CFSG.KD.Co2KX3.loC 0)) (CFSG.KD.Co2KX3.loC 0))
    (CFSG.KD.Co2KX3.accC 0)) (CFSG.KD.Co2KX3.accC 7) = true :=
  cover_chain _ _ _ _ _ _ _ 7 CFSG.KD.Co2KX3.okC_all

theorem BPfacts : Nat.beq (runFacts CFSG.KD.Co2BP.blk CFSG.KD.Co2BP.selWT CFSG.KD.Co2BP.INV
    CFSG.KD.Co2BP.nC (nat_lit 4) (seg CFSG.KD.Co2BP.JF
      (Nat.sub (CFSG.KD.Co2BP.loF 176) (CFSG.KD.Co2BP.loF 0)) (CFSG.KD.Co2BP.loF 0))
    (CFSG.KD.Co2BP.accF 0)) (CFSG.KD.Co2BP.accF 176) = true :=
  facts_chain _ _ _ _ _ _ _ _ 176 CFSG.KD.Co2BP.okW_all

end CertificateChecks.KernelCo2

end
