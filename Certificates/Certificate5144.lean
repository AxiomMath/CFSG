module

public import CFSG.GH74.GLS.C3.Layer2.L5C2gTableInputs
import CFSG.Certificates.Kernel.L5.BaseMul
import CFSG.Certificates.Kernel.L5.EngOne
import CFSG.Certificates.Kernel.L5.F5Code
import Certificates.Kernel.L5.Sh1Codes
import Certificates.Kernel.L5.Sh1Base
import Certificates.Kernel.L5.Sh1Fus
import Certificates.Kernel.L5.Sh1Rec
import Certificates.Kernel.L5.Sh1Eng
import Certificates.Kernel.L5.Sh1Post
import Certificates.Kernel.L5.Sh2FusE

open Equiv CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus
  CFSG.KD CFSG.KD.L5 CFSG.KD.L5.Sh1

namespace CertificateChecks.Batch5144

open Equiv CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus
  CFSG.KD CFSG.KD.L5 CFSG.KD.L5.Sh1


theorem codesM : codesChk (fun m : ↥Sh1 => m.1) sh1M Sh1R.C = true := by
  have h := codes1
  simp only [codesChk, decide_eq_true_eq] at h ⊢
  have hl : sh1M.length = sh1WW.length := List.length_pmap
  rw [hl, ← h]
  exact sh1M_codes

theorem one1_mul : mulBN 128 Sh1R.C Sh1R.K 7 0 6 0 0 = 0 := by
  decide +kernel

theorem mkTabData_n {M : Type} [Group M] [DecidableEq M] (elems : List M) (code : M → Nat)
    (hc : ∀ m : M, m ∈ elems) (tab invT : Array Nat) (oneI : Nat)
    (hchk : tabCheck elems code tab invT oneI = true) :
    (mkTabData elems code hc tab invT oneI hchk).n = elems.length := rfl

theorem sh1D_n : sh1D.n = 128 := by
  unfold sh1D
  rw [mkTabData_n]
  exact sh1M_length

theorem codeP16_inj {p q : Perm (Fin 16)} (h : codeP16 p = codeP16 q) : p = q := by
  refine Equiv.ext fun i => Fin.ext ?_
  have hi := dg_codeP16 p i
  rw [h, dg_codeP16] at hi
  exact hi.symm

theorem chk_of (D : TabData ↥Sh1) (hn : D.n = 128) (he : ∀ a : Idx D.n, D.e a = sh1M.getD a.v 1) :
    (let _i : Group (Idx D.n) := D.grp
    engOK (engOf D embHom1) && decide (survivors (engOf D embHom1) = [[0, 0, 2, 0, 2, 2]]) &&
      (List.finRange 16).any fun a => (List.finRange 16).any fun b =>
        isInv (D.idx (embHom1 (elT a))) && isInv (D.idx (embHom1 (elT b))) &&
          decide (blkOf (engOf D embHom1).ciA [0, 0, 2, 0, 2, 2] (D.idx (embHom1 (elT a))) =
            blkOf (engOf D embHom1).ciA [0, 0, 2, 0, 2, 2] (D.idx (embHom1 (elT b)))) &&
          !(n24L.any fun A => decide (A a = b))) = true := by
  obtain ⟨n, e, idxFn, tab, invT, oneI, s1, s2, s3, s4, s5, s6, s7⟩ := D
  subst hn
  set D : TabData ↥Sh1 := ⟨128, e, idxFn, tab, invT, oneI, s1, s2, s3, s4, s5, s6, s7⟩ with hD
  let _i : Group (Idx 128) := D.grp
  have hC : ∀ a : Idx D.n, codeP16 (Sh1.subtype (D.e a)) = cget Sh1R.C 64 a.v := fun a => by
    have hlt : a.v < sh1M.length := by
      rw [sh1M_length]
      exact a.v_lt
    have h1 := codes_of codesM hlt
    rw [he a, Subgroup.coe_subtype]
    exact h1
  have hm : ∀ a b, mul1 a b = D.grp.mul a b :=
    mulB_eq D Sh1.subtype (by decide) (by decide) hC (key_of key1)
  have hoo : mul1 one1 one1 = one1 := Idx.ext one1_mul
  have ho : one1 = D.grp.one := by
    have h := hm one1 one1
    rw [hoo] at h
    exact mul_left_cancel (a := one1) (h.symm.trans (mul_one one1).symm)
  have hi : ∀ a, inv1 a = D.grp.inv a := invB_eq D.grp hm (by rw [← ho]; rfl) inv1_chk
  have hgrp : grpOf D.grp mul1 hm inv1 hi one1 ho = D.grp := grpOf_eq _ _ _ _ _ _ _
  let emb : ↥T5 →* Idx 128 := D.iso.toMonoidHom.comp embHom1
  have hE : ∀ t, D.idx (embHom1 t) = embL1 t := fun t => by
    have h := embL1_chk
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    have h2 := h t (List.mem_pmap.2 ⟨t.1, mem_allT5.2 t.2, rfl⟩)
    have h3 : D.e (embL1 t) = embHom1 t :=
      Subtype.ext (codeP16_inj (by rw [← h2]; exact hC (embL1 t)))
    rw [← h3, D.idx_e]
  have hEf : (⇑emb : ↥T5 → Idx 128) = embL1 := funext fun t => hE t
  have hf0 := fus1 D.grp hm hi ho
  rw [hgrp] at hf0
  have hf : fusChk emb eng1R.reps eng1R.ciA eng1R.invs eng1R.x = true := by
    have he1 : embL1 = fun t => eI1 (codeP t.1) := rfl
    rw [fusChk_eq, hEf, he1, f5PairsF_eq eI1 _ _ Sh2Fus.tC_chk Sh2Fus.f5C_chk]
    exact hf0
  have hci : (engOf D embHom1).ciA = eng1R.ciA := by
    have h := hf
    simp only [fusChk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact h3
  have hc := csz1 D.grp hm hi ho
  have hg := mgens1_chk D.grp hm hi ho
  have hmg := mg1 D.grp hm hi ho
  have hx := ctx1_chk D.grp hm hi ho
  have hR := ctxR1 D.grp hm hi ho
  have hs := surv1 D.grp hm hi ho
  have hw := wit1 D.grp hm hi ho
  have hp := post1 D.grp hm hi ho
  rw [hgrp] at hc hg hmg hx hR hs hw hp
  have hmain := engChk_of1 (emb := emb) eng1R mgens1 ctx1 ld1 paths1 Sh1R.tags hf hc hg hmg hx hR
    hs hw
  simp only [Bool.and_eq_true] at hmain ⊢
  refine ⟨hmain, ?_⟩
  simp only [hE, hci]
  exact hp

end CertificateChecks.Batch5144

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
theorem certificate5144 :     chk1 = true := by
  exact CertificateChecks.Batch5144.chk_of sh1D CertificateChecks.Batch5144.sh1D_n
    (mkTabData_e sh1M sh1Code sh1M_complete _ _ _ sh1_chk)

end Certificates
