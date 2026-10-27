module

public import Certificates.Data.Kernel.LceSTab
public import Certificates.Data.Kernel.LceSHeRu
public import Certificates.Kernel.CosetJ.Suz2Labs
public import Certificates.Kernel.CosetJ.Suz2Facts
import Certificates.Kernel.HeRu.Assemble
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TL0
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TL1

public section

namespace CertificateChecks.KernelCosetJ.Suz2

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceSeg

theorem TL.allL : ∀ i < 976, CFSG.KD.CJSuz2T.okL i = true :=
  forall_append 488 488 CFSG.KD.CJSuz2T.okL_0 CFSG.KD.CJSuz2T.okL_1

theorem TL.labs : Nat.beq (CFSG.KC.LabF.runLab CFSG.KD.CJSuz2T.selWT CFSG.KD.CJSuz2T.LB
    CFSG.KD.CJSuz2T.HS
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0)) (CFSG.KD.CJSuz2T.accL 0)) (CFSG.KD.CJSuz2T.accL 976) = true :=
  labF_chain _ _ _ _ _ _ 976 TL.allL

theorem TL.ids : Nat.beq (CFSG.KC.LceSR.runIds CFSG.KD.CJSuz2T.selWT (nat_lit 2048)
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0)) (nat_lit 1)) (nat_lit 1) = true := by quickRfl

theorem TL.ok : CFSG.Certificates.LS.LabF.labOk CFSG.KD.CJSuz2T.blk CFSG.KD.CJSuz2T.selWT
    CFSG.KD.CJSuz2T.selRT CFSG.KD.CJSuz2T.selST CFSG.KD.CJSuz2T.LB CFSG.KD.CJSuz2T.INV
    CFSG.KD.CJSuz2T.INV8 (nat_lit 10) CFSG.KD.CJSuz2T.nC (nat_lit 293298) (nat_lit 1169643)
    (nat_lit 2048) CFSG.KD.CJSuz2T.HS (nat_lit 90) (nat_lit 1) (nat_lit 1)
    (CFSG.KD.CJSuz2T.accF 0) (CFSG.KD.CJSuz2T.accF 976) (CFSG.KD.CJSuz2T.accL 0)
    (CFSG.KD.CJSuz2T.accL 976)
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0)) = true :=
  CFSG.Certificates.LS.LabF.labOk_intro CFSG.KD.CJSuz2T.sH0 T.hints T.norm CFSG.KD.CJSuz2T.sH1
    CFSG.KD.CJSuz2T.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) CFSG.KD.CJSuz2T.sH6 TL.labsWF TL.ids T.facts TL.labs

end CertificateChecks.KernelCosetJ.Suz2

end
