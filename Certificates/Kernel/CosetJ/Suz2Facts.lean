module

public import Certificates.Data.Kernel.LceSTab
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Route
public import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TH
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TW0
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TW1
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TW2
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TW3
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TC
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.B

public section

namespace CertificateChecks.KernelCosetJ.Suz2

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceSeg

theorem T.hints : CFSG.KC.Bind.hintsOK CFSG.KD.CJSuz2T.selWT (nat_lit 2048) (nat_lit 90)
    (nat_lit 1) CFSG.KD.CJSuz2T.HS = true := by quickRfl

theorem T.per : CFSG.Certificates.LCE.wtPer CFSG.KD.CJSuz2T.selWT (nat_lit 2048) = true := by
  quickRfl

theorem T.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.CJSuz2T.selRT (nat_lit 90) = true := by
  quickRfl

theorem T.allW : ∀ i < 976, CFSG.KD.CJSuz2T.okW i = true :=
  forall_append 768 208
    (forall_append 512 256 (forall_append 256 256 CFSG.KD.CJSuz2T.okW_0 CFSG.KD.CJSuz2T.okW_1)
      CFSG.KD.CJSuz2T.okW_2) CFSG.KD.CJSuz2T.okW_3

theorem T.facts : Nat.beq (runFacts CFSG.KD.CJSuz2T.blk CFSG.KD.CJSuz2T.selWT CFSG.KD.CJSuz2T.INV
    CFSG.KD.CJSuz2T.nC (nat_lit 10)
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0)) (CFSG.KD.CJSuz2T.accF 0)) (CFSG.KD.CJSuz2T.accF 976) = true :=
  facts_chain _ _ _ _ _ _ _ _ 976 T.allW

theorem T.cover : Nat.beq (runCover CFSG.KD.CJSuz2T.blk CFSG.KD.CJSuz2T.LVs (nat_lit 1169643)
    (nat_lit 10)
    (seg CFSG.KD.CJSuz2T.JV (Nat.sub (CFSG.KD.CJSuz2T.loC 83) (CFSG.KD.CJSuz2T.loC 0))
      (CFSG.KD.CJSuz2T.loC 0)) (CFSG.KD.CJSuz2T.accC 0)) (CFSG.KD.CJSuz2T.accC 83) = true :=
  cover_chain _ _ _ _ _ _ _ 83 CFSG.KD.CJSuz2T.okC_all

theorem T.ok : CFSG.Certificates.LCE.lceOk CFSG.KD.CJSuz2T.blk CFSG.KD.CJSuz2T.selWT
    CFSG.KD.CJSuz2T.selRT CFSG.KD.CJSuz2T.selST CFSG.KD.CJSuz2T.LVs CFSG.KD.CJSuz2T.INV
    CFSG.KD.CJSuz2T.INV8 (nat_lit 10) CFSG.KD.CJSuz2T.nC (nat_lit 293298) (nat_lit 72)
    CFSG.KD.CJSuz2T.nLive (nat_lit 2048) CFSG.KD.CJSuz2T.HS (nat_lit 90) (nat_lit 1)
    (nat_lit 1169643)
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0))
    (seg CFSG.KD.CJSuz2T.JV (Nat.sub (CFSG.KD.CJSuz2T.loC 83) (CFSG.KD.CJSuz2T.loC 0))
      (CFSG.KD.CJSuz2T.loC 0))
    (CFSG.KD.CJSuz2T.accF 0) (CFSG.KD.CJSuz2T.accF 976) (CFSG.KD.CJSuz2T.accC 0)
    (CFSG.KD.CJSuz2T.accC 83) = true :=
  CFSG.Certificates.LCE.lceOk_intro CFSG.KD.CJSuz2T.sH1 CFSG.KD.CJSuz2T.sH0 T.hints
    CFSG.KD.CJSuz2T.sH2 CFSG.KD.CJSuz2T.sH3 (by quickRfl) (by quickRfl) (by quickRfl) T.per
    T.norm (by quickRfl) T.facts (by quickRfl) (by quickRfl) T.cover (by quickRfl)

theorem B.hints : CFSG.KC.Bind.hintsOK CFSG.KD.CJSuz2B.selWT (nat_lit 8) (nat_lit 4) (nat_lit 1)
    CFSG.KD.CJSuz2B.HS = true := by quickRfl

theorem B.per : CFSG.Certificates.LCE.wtPer CFSG.KD.CJSuz2B.selWT (nat_lit 8) = true := by
  quickRfl

theorem B.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.CJSuz2B.selRT (nat_lit 4) = true := by
  quickRfl

theorem B.facts : Nat.beq (runFacts CFSG.KD.CJSuz2B.blk CFSG.KD.CJSuz2B.selWT CFSG.KD.CJSuz2B.INV
    CFSG.KD.CJSuz2B.nC (nat_lit 2)
    (seg CFSG.KD.CJSuz2B.JF (Nat.sub (CFSG.KD.CJSuz2B.loF 1) (CFSG.KD.CJSuz2B.loF 0))
      (CFSG.KD.CJSuz2B.loF 0)) (CFSG.KD.CJSuz2B.accF 0)) (CFSG.KD.CJSuz2B.accF 1) = true :=
  facts_chain _ _ _ _ _ _ _ _ 1 CFSG.KD.CJSuz2B.okW_all

theorem B.cover : Nat.beq (runCover CFSG.KD.CJSuz2B.blk CFSG.KD.CJSuz2B.LVs (nat_lit 1) (nat_lit 2)
    (seg CFSG.KD.CJSuz2B.JV (Nat.sub (CFSG.KD.CJSuz2B.loC 1) (CFSG.KD.CJSuz2B.loC 0))
      (CFSG.KD.CJSuz2B.loC 0)) (CFSG.KD.CJSuz2B.accC 0)) (CFSG.KD.CJSuz2B.accC 1) = true :=
  cover_chain _ _ _ _ _ _ _ 1 CFSG.KD.CJSuz2B.okC_all

theorem B.ok : CFSG.Certificates.LCE.lceOk CFSG.KD.CJSuz2B.blk CFSG.KD.CJSuz2B.selWT
    CFSG.KD.CJSuz2B.selRT CFSG.KD.CJSuz2B.selST CFSG.KD.CJSuz2B.LVs CFSG.KD.CJSuz2B.INV
    CFSG.KD.CJSuz2B.INV8 (nat_lit 2) CFSG.KD.CJSuz2B.nC (nat_lit 1) (nat_lit 1)
    CFSG.KD.CJSuz2B.nLive (nat_lit 8) CFSG.KD.CJSuz2B.HS (nat_lit 4) (nat_lit 1) (nat_lit 1)
    (seg CFSG.KD.CJSuz2B.JF (Nat.sub (CFSG.KD.CJSuz2B.loF 1) (CFSG.KD.CJSuz2B.loF 0))
      (CFSG.KD.CJSuz2B.loF 0))
    (seg CFSG.KD.CJSuz2B.JV (Nat.sub (CFSG.KD.CJSuz2B.loC 1) (CFSG.KD.CJSuz2B.loC 0))
      (CFSG.KD.CJSuz2B.loC 0))
    (CFSG.KD.CJSuz2B.accF 0) (CFSG.KD.CJSuz2B.accF 1) (CFSG.KD.CJSuz2B.accC 0)
    (CFSG.KD.CJSuz2B.accC 1) = true :=
  CFSG.Certificates.LCE.lceOk_intro CFSG.KD.CJSuz2B.sH1 CFSG.KD.CJSuz2B.sH0 B.hints
    CFSG.KD.CJSuz2B.sH2 CFSG.KD.CJSuz2B.sH3 (by quickRfl) (by quickRfl) (by quickRfl) B.per
    B.norm (by quickRfl) B.facts (by quickRfl) (by quickRfl) B.cover (by quickRfl)

end CertificateChecks.KernelCosetJ.Suz2

end
