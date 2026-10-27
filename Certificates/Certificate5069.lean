module

public import CFSG.GH74.GLS.C3.Layer2.L5C5g
public import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C5fInputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5065
public import Certificates.Certificate5066
import CFSG.Certificates.Kernel.L5.EngRec
import CFSG.Certificates.Kernel.L5.F5Code
import CFSG.Certificates.Kernel.L5.Sh2Grp
import Certificates.Kernel.L5.Sh2MulChecks
import Certificates.Kernel.L5.Sh2Eng0
import Certificates.Kernel.L5.Sh2Eng1
import Certificates.Kernel.L5.Sh2Eng2
import Certificates.Kernel.L5.Sh2Eng3
import Certificates.Kernel.L5.Sh2Rec0
import Certificates.Kernel.L5.Sh2Rec1
import Certificates.Kernel.L5.Sh2Rec2
import Certificates.Kernel.L5.Sh2Rec3
import Certificates.Kernel.L5.Sh2FusE
import Certificates.Kernel.L5.Sh2Fus0
import Certificates.Kernel.L5.Sh2Fus1
import Certificates.Kernel.L5.Sh2Fus2
import Certificates.Kernel.L5.Sh2Fus3

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD
  CFSG.KD.L5 CFSG.Certificates.Kernel.L5Sh2

namespace CertificateChecks.Batch5069

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD
  CFSG.KD.L5 CFSG.Certificates.Kernel.L5Sh2

local macro "tr " c:term:max ty:term:max : tactic => `(tactic|
  exact (grpOf_eq (sh2TabD $ty).grp (mulI (Fin.val $ty)) (mulI_eq' sh2MulChk_true $ty)
    (invI (Fin.val $ty)) (invI_eq sh2MulChk_true $ty) oneI (oneI_eq $ty)) ▸
    ($c (sh2TabD $ty).grp (mulI_eq' sh2MulChk_true $ty) (invI_eq sh2MulChk_true $ty)
      (oneI_eq $ty)))


theorem idx_ext {a b : Idx 256} (h : a.v = b.v) : a = b := by
  cases a
  cases b
  congr
  exact Fin.ext h

theorem embI_eq (ty : Fin 4) : (fun t => (sh2TabD ty).idx (inc ty (embHom0 t))) = embL := by
  funext t
  have h := Sh2Fus.embL_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact idx_ext (h ty (List.mem_finRange ty) t (List.mem_pmap.2 ⟨t.1, mem_allT5.2 t.2, rfl⟩))

theorem fusChk_embL (ty : Fin 4) (d : Eng 256)
    (hf : @fusChkL 256 (sh2TabD ty).grp
      (@fuseL 256 (sh2TabD ty).grp (f5P eI (Sh2FusT.embT.map Prod.fst) Sh2FusT.f5C)
        (nbarPairsF embL)) (embL x0T5) d.reps d.ciA d.invs d.x = true) :
    @fusChk 256 (sh2TabD ty).grp embL d.reps d.ciA d.invs d.x = true := by
  have he : embL = fun t => eI (codeP t.1) := rfl
  rw [@fusChk_eq 256 (sh2TabD ty).grp, he, f5PairsF_eq eI _ _ Sh2Fus.tC_chk Sh2Fus.f5C_chk]
  exact hf

theorem sh2EngChk_of (ty : Fin 4) (d : Eng 256) (mg : List (Idx 256))
    (Rs : List (List (Idx 256))) (ws : List (List Nat))
    (hf : @fusChkL 256 (sh2TabD ty).grp
      (@fuseL 256 (sh2TabD ty).grp (f5P eI (Sh2FusT.embT.map Prod.fst) Sh2FusT.f5C)
        (nbarPairsF embL)) (embL x0T5) d.reps d.ciA d.invs d.x = true)
    (hc : @cszChk 256 (sh2TabD ty).grp d.cszA = true)
    (hg : @genChk 256 (sh2TabD ty).grp (elemsI 256) [] mg = true)
    (hm : @mgChk 256 (sh2TabD ty).grp mg d.maxSubs = true)
    (hx : @ctxGensChk 256 (sh2TabD ty).grp d.reps Rs = true)
    (hR : @ctxChk 256 (sh2TabD ty).grp d.reps Rs = true)
    (hw : @allWit 256 (sh2TabD ty).grp d ws = true) : sh2EngChk ty = true := by
  let _i : Group (Idx (sh2TabD ty).n) := (sh2TabD ty).grp
  let emb : ↥T5 →* Idx (sh2TabD ty).n :=
    (sh2TabD ty).iso.toMonoidHom.comp ((inc ty).comp embHom0)
  have hE : (fun t => emb t) = embL := by
    funext t
    exact congrFun (embI_eq ty) t
  have hf := fusChk_embL ty d hf
  rw [← hE] at hf
  exact @engChk_of 256 (sh2TabD ty).grp emb d mg Rs ws hf hc hg hm hx hR hw

theorem sh2EngChk_0 : sh2EngChk 0 = true :=
  sh2EngChk_of 0 (engA 0) mgensR ctxA tagsA
    (by tr Sh2Fus.fus0 (0 : Fin 4))
    (by tr Sh2Rec.csz0 (0 : Fin 4))
    (by tr Sh2Eng.mgens0 (0 : Fin 4))
    (by tr Sh2Rec.mg0 (0 : Fin 4))
    (by tr Sh2Eng.ctx0 (0 : Fin 4))
    (by tr Sh2Rec.ctxR0 (0 : Fin 4))
    (by tr Sh2Eng.wit0 (0 : Fin 4))

theorem sh2EngChk_1 : sh2EngChk 1 = true :=
  sh2EngChk_of 1 (engB 1) mgensR ctxB tagsB
    (by tr Sh2Fus.fus1 (1 : Fin 4))
    (by tr Sh2Rec.csz1 (1 : Fin 4))
    (by tr Sh2Eng.mgens1 (1 : Fin 4))
    (by tr Sh2Rec.mg1 (1 : Fin 4))
    (by tr Sh2Eng.ctx1 (1 : Fin 4))
    (by tr Sh2Rec.ctxR1 (1 : Fin 4))
    (by tr Sh2Eng.wit1 (1 : Fin 4))

theorem sh2EngChk_2 : sh2EngChk 2 = true :=
  sh2EngChk_of 2 (engA 2) mgensR ctxA tagsA
    (by tr Sh2Fus.fus2 (2 : Fin 4))
    (by tr Sh2Rec.csz2 (2 : Fin 4))
    (by tr Sh2Eng.mgens2 (2 : Fin 4))
    (by tr Sh2Rec.mg2 (2 : Fin 4))
    (by tr Sh2Eng.ctx2 (2 : Fin 4))
    (by tr Sh2Rec.ctxR2 (2 : Fin 4))
    (by tr Sh2Eng.wit2 (2 : Fin 4))

theorem sh2EngChk_3 : sh2EngChk 3 = true :=
  sh2EngChk_of 3 (engB 3) mgensR ctxB tagsB
    (by tr Sh2Fus.fus3 (3 : Fin 4))
    (by tr Sh2Rec.csz3 (3 : Fin 4))
    (by tr Sh2Eng.mgens3 (3 : Fin 4))
    (by tr Sh2Rec.mg3 (3 : Fin 4))
    (by tr Sh2Eng.ctx3 (3 : Fin 4))
    (by tr Sh2Rec.ctxR3 (3 : Fin 4))
    (by tr Sh2Eng.wit3 (3 : Fin 4))

end CertificateChecks.Batch5069

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
theorem certificate5069 : (List.finRange 4).all sh2EngChk = true := by
  rw [List.all_eq_true]
  intro ty _
  fin_cases ty
  exacts [CertificateChecks.Batch5069.sh2EngChk_0, CertificateChecks.Batch5069.sh2EngChk_1, CertificateChecks.Batch5069.sh2EngChk_2,
    CertificateChecks.Batch5069.sh2EngChk_3]

end Certificates
