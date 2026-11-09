module

public import Certificates.Data.Kernel.LceSTab
public import Certificates.Data.Kernel.LceSHeRu
public import Certificates.Kernel.CosetJ.Suz2Labs
public import Certificates.Kernel.CosetJ.Suz2Facts
import Certificates.Kernel.HeRu.Assemble
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TL0
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TL1
public import CFSG.Certificates.Kernel.LceSP.LabFLabM

public section

namespace CertificateChecks.KernelCosetJ.Suz2

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceSeg

theorem TL.allLM : ∀ i < 976, CFSG.KD.CJSuz2T.okLM i = true :=
  forall_append 488 488 CFSG.KD.CJSuz2T.okLM_0 CFSG.KD.CJSuz2T.okLM_1

theorem TL.labsM : Nat.beq (CFSG.KC.LabM.runLabM CFSG.KD.CJSuz2T.selWT CFSG.KD.CJSuz2T.LB
    CFSG.KD.CJSuz2T.MB CFSG.KD.CJSuz2T.HS
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0)) (CFSG.KD.CJSuz2T.accL 0)) (CFSG.KD.CJSuz2T.accL 976) = true :=
  slOK_chain_beq _ (fun _ => rfl) (CFSG.KC.LabM.runLabM_append _ _ _ _) _ _ _ 976 TL.allLM

theorem runIds_append (WT : Nat → Nat) (m : Nat) :
    ∀ l1 l2 x, CFSG.KC.LceSR.runIds WT m (List.append l1 l2) x =
      CFSG.KC.LceSR.runIds WT m l2 (CFSG.KC.LceSR.runIds WT m l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change CFSG.KC.Loop.strictN (CFSG.KC.LceSR.idsChunk WT m C x)
        (CFSG.KC.LceSR.runIds WT m (List.append l1 l2)) =
      CFSG.KC.LceSR.runIds WT m l2 (CFSG.KC.Loop.strictN (CFSG.KC.LceSR.idsChunk WT m C x)
        (CFSG.KC.LceSR.runIds WT m l1))
    have e (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by cases y <;> rfl
    rw [e, e, runIds_append WT m l1 l2]

@[expose] noncomputable def TL.okI (i : Nat) : Bool :=
  slOK (CFSG.KC.LceSR.runIds CFSG.KD.CJSuz2T.selWT (nat_lit 2048)) CFSG.KD.CJSuz2T.JF
    CFSG.KD.CJSuz2T.loF (fun _ => nat_lit 1) i

theorem TL.allI : ∀ t < 976, TL.okI t = true := by
  kc_cover 16

theorem chain_beq_const (F : List Nat → Nat → Nat) (hF0 : ∀ x, F [] x = x)
    (hF : ∀ (l1 l2 : List Nat) (x : Nat), F (List.append l1 l2) x = F l2 (F l1 x))
    (f lo : Nat → Nat) (c n : Nat) (h : ∀ i < n, slOK F f lo (fun _ => c) i = true) :
    Nat.beq (F (seg f (Nat.sub (lo n) (lo 0)) (lo 0)) c) c = true :=
  slOK_chain_beq F hF0 hF f lo (fun _ => c) n h

theorem TL.ids : Nat.beq (CFSG.KC.LceSR.runIds CFSG.KD.CJSuz2T.selWT (nat_lit 2048)
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0)) (nat_lit 1)) (nat_lit 1) = true :=
  chain_beq_const (CFSG.KC.LceSR.runIds CFSG.KD.CJSuz2T.selWT (nat_lit 2048)) (fun _ => rfl)
    (runIds_append CFSG.KD.CJSuz2T.selWT (nat_lit 2048)) CFSG.KD.CJSuz2T.JF CFSG.KD.CJSuz2T.loF
    (nat_lit 1) 976 TL.allI

theorem TL.ok : CFSG.Certificates.LceP.LabFM.labOkM CFSG.KD.CJSuz2T.blk CFSG.KD.CJSuz2T.selWT
    CFSG.KD.CJSuz2T.selRT CFSG.KD.CJSuz2T.selST CFSG.KD.CJSuz2T.LB CFSG.KD.CJSuz2T.MB
    CFSG.KD.CJSuz2T.INV
    CFSG.KD.CJSuz2T.INV8 (nat_lit 10) CFSG.KD.CJSuz2T.nC (nat_lit 293298) (nat_lit 1169643)
    (nat_lit 2048) CFSG.KD.CJSuz2T.HS (nat_lit 90) (nat_lit 1) (nat_lit 1)
    (CFSG.KD.CJSuz2T.accF 0) (CFSG.KD.CJSuz2T.accF 976) (CFSG.KD.CJSuz2T.accL 0)
    (CFSG.KD.CJSuz2T.accL 976)
    (seg CFSG.KD.CJSuz2T.JF (Nat.sub (CFSG.KD.CJSuz2T.loF 976) (CFSG.KD.CJSuz2T.loF 0))
      (CFSG.KD.CJSuz2T.loF 0)) = true :=
  CFSG.Certificates.LceP.LabFM.labOkM_intro CFSG.KD.CJSuz2T.sH0 T.hints T.norm
    CFSG.KD.CJSuz2T.sH1 CFSG.KD.CJSuz2T.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) CFSG.KD.CJSuz2T.sH6 TL.labsWF TL.ids T.facts TL.labsM

end CertificateChecks.KernelCosetJ.Suz2

end
