module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C2fInputs
public import CFSG.GH74.GLS.C3.Layer2.L5C2fTableInputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5056
import CFSG.Certificates.Kernel.L5.BaseMul
import CFSG.Certificates.Kernel.L5.EngOne
import CFSG.Certificates.Kernel.L5.F5Code
import CFSG.Certificates.Kernel.Common.DecideFV
import Certificates.Kernel.L5.Sh2FusE
import Certificates.Kernel.L5.Eng0Base
import Certificates.Kernel.L5.Eng0Emb
import Certificates.Kernel.L5.Eng0Fus
import Certificates.Kernel.L5.Eng0Rec
import Certificates.Kernel.L5.Eng0Gen
import Certificates.Kernel.L5.Eng0Surv
import Certificates.Kernel.L5.Eng0Wit
import Certificates.Kernel.L5.Eng0Post

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

namespace CertificateChecks.Batch5142

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

set_option hygiene false in
local macro "tr " c:term:max : tactic => `(tactic|
  exact (grpOf_eq G E0.mul hm E0.inv inv_eq E0.one ho) ▸ ($c G hm inv_eq ho))


theorem chk_of {n : Nat} (hn : n = 128) [G : Group (Idx n)] (emb : ↥T5 →* Idx n)
    (r : Idx n → Bool) (hm0 : ∀ a b, mulB n E0.codesP E0.keyP 7 0 6 a b = G.mul a b)
    (hi0 : ∀ a, invB n E0.invP 7 a = G.inv a) (ho0 : G.one.v = 0)
    (hE : ∀ t, (emb t).v = (E0.embL t).v) (hr : ∀ u, r u = E0.r1P.testBit u.v) :
    (engOK (mkEng emb) && decide (survivors (mkEng emb) = [E0.ld0]) &&
      (mkEng emb).invs.all fun u => (mkEng emb).invs.all fun v =>
        !r u || !decide (blkOf (mkEng emb).ciA E0.ld0 u = blkOf (mkEng emb).ciA E0.ld0 v) ||
          r v) = true := by
  subst hn
  obtain rfl : r = fun u => E0.r1P.testBit u.v := funext hr
  have hm : ∀ a b, E0.mul a b = G.mul a b := hm0
  have inv_eq : ∀ a, E0.inv a = G.inv a := hi0
  have ho : E0.one = G.one := Idx.ext (by rw [ho0]; rfl)
  have hE' : (fun t => emb t) = E0.embL := funext fun t => Idx.ext (hE t)
  have htC : allT5L.map (fun t : ↥T5 => codeP t.1) = E0.embT.map Prod.fst :=
    Sh2Fus.tC_chk.trans E0.tC_chk.symm
  have hf : fusChk E0.embL E0.eng.reps E0.eng.ciA E0.eng.invs E0.eng.x = true := by
    have he : E0.embL = fun t => E0.eI (codeP t.1) := rfl
    rw [fusChk_eq, he, f5PairsF_eq E0.eI _ _ htC Sh2Fus.f5C_chk]
    exact (grpOf_eq G E0.mul hm E0.inv inv_eq E0.one ho) ▸ (E0.fus0 G hm inv_eq ho)
  rw [← hE'] at hf
  have h1 := engChk_of1 (emb := emb) E0.eng E0.mgens E0.ctxs E0.ld0 E0.paths E0.tags hf
    (by tr E0.csz0) (by tr E0.mgens0) (by tr E0.mg0) (by tr E0.ctx0) (by tr E0.ctxR0)
    (by tr E0.surv0) (by tr E0.wit0)
  simp only [fusChk, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hiv, -⟩, hci⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have ei : (mkEng emb).invs = E0.eng.invs := hiv
  have ec : (mkEng emb).ciA = E0.eng.ciA := hci
  rw [Bool.and_eq_true]
  refine ⟨h1, ?_⟩
  rw [ei, ec]
  exact E0.post0


theorem chk0_true : chk0 = true := by
  have ho : sh0D.grp.one.v = 0 := by kc_decide_fv
  have hn : sh0D.n = 128 := rfl
  have hC : ∀ a : Idx sh0D.n, codeP16 (Sh0.subtype (sh0D.e a)) = cget E0.codesP 64 a.v := by
    intro a
    have he : sh0D.e a = sh0M.getD a.v 1 :=
      mkTabData_e sh0M sh0Code sh0M_complete _ _ _ sh0_chk a
    rw [he]
    exact codes_of E0.codes_chk a.v_lt
  have hK := key_of (n := sh0D.n) (by rw [hn]; exact E0.key_chk)
  have hm := mulB_eq sh0D Sh0.subtype (by decide) (by decide) hC hK
  have hi := invB_eq sh0D.grp hm ho (by rw [hn]; exact E0.inv_chk)
  have hE : ∀ t, (sh0D.idx (embHom0 t)).v = (E0.embL t).v := by
    intro t
    have h := E0.embL_chk
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact h t (List.mem_pmap.2 ⟨t.1, mem_allT5.2 t.2, rfl⟩)
  have hr : ∀ u : Idx sh0D.n, isR1 u = E0.r1P.testBit u.v := by
    have h := E0.r1_chk
    simp only [List.all_eq_true, beq_iff_eq] at h
    exact fun u => h u (mem_elemsI u)
  let _i : Group (Idx sh0D.n) := sh0D.grp
  exact chk_of (G := sh0D.grp) hn (sh0D.iso.toMonoidHom.comp embHom0) isR1 hm hi ho hE hr

end CertificateChecks.Batch5142

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Fus in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5142 :     chk0 = true := by
  exact CertificateChecks.Batch5142.chk0_true

end Certificates
