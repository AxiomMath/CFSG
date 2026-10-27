module

public import CFSG.GH74.GLS.C3.Prop121.Card7F3Inputs
import CFSG.Certificates.Kernel.PermCent.F7CentChkSound
import Certificates.Kernel.Card7F.InvChecks
public import Certificates.Data.Kernel.PermCent.CV

public section

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF CFSG.Certificates.Kernel.PkCV

namespace CertificateChecks.Batch5077

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF CFSG.Certificates.Kernel.PkCV

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.FF in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem facts : (∀ p ∈ PL, (p.1 * p.2) ^ 12 = 1)
    ∧ (PL.countP (fun p => powB 12 (p.1 * p.2) x0F) = 27)
    ∧ ((CYL f0).countP (fun b => decide (ccardB f0 b = 96)) = 3)
    ∧ ((CYL f0).countP (fun b => decide (ccardB f0 b = 48)) = 6)
    ∧ (∀ b ∈ CYL f0, ccardB f0 b = 96 ∨ ccardB f0 b = 48)
    ∧ (∀ b ∈ CYL g0, ccardB g0 b = 12) := by
  have h := Certificates.Kernel.Card7F.inv_chk
  unfold f7InvChkAt f7InvChk at h
  rw [forceQL_eq, forceQL_eq, forceQL_eq, forceQL_eq, forceQL_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hF := forall2_CL f0 _ rfl
  have hG := forall2_CL g0 _ rfl
  have hX : List.Forall₂ RelP (CXL f0) ((CF7 (cOf (swap 0 1 * swap 1 2))).filter fun x => invP x 4) :=
    f2_filter hF fun _ _ hc => decide_XF hc
  have hY : List.Forall₂ RelP (CYL f0) ((CF7 (cOf (swap 0 1 * swap 1 2))).filter fun x => invP x 8) :=
    f2_filter hF fun _ _ hc => decide_YF hc
  have hYg : List.Forall₂ RelP (CYL g0)
      ((CF7 (cOf (swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)))).filter fun x => invP x 8) :=
    f2_filter hG fun _ _ hc => decide_YF hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (CXL f0).all (fun a => (CYL f0).all fun b => decide ((a * b) ^ 12 = 1)) = true := by
      rw [f2_all hX fun a x ha => f2_all hY fun b y hb => decide_pow ha hb relP_one 12]
      exact h1
    intro p hp
    obtain ⟨ha, hb⟩ := List.mem_product.1 hp
    exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 e _ ha) _ hb)
  · unfold PL
    refine (f2_countP (f2_product hX hY) (Q := fun p => (List.range 12).any fun n =>
      powP p.1 p.2 n (1, cOf x4)) fun p q hpq => ?_).trans h2
    unfold powB
    exact congrArg (List.any (List.range 12)) (funext fun n => decide_pow hpq.1 hpq.2 relP_x0F n)
  · refine (f2_countP hY (Q := fun y => decide (cntP (CF7 (cOf (swap 0 1 * swap 1 2))) y = 96))
      fun b y hb => ?_).trans h3
    rw [ccardB_eq_cntP hF hb]
  · refine (f2_countP hY (Q := fun y => decide (cntP (CF7 (cOf (swap 0 1 * swap 1 2))) y = 48))
      fun b y hb => ?_).trans h4
    rw [ccardB_eq_cntP hF hb]
  · have e : (CYL f0).all (fun b => decide (ccardB f0 b = 96 ∨ ccardB f0 b = 48)) = true := by
      refine (f2_all hY (Q := fun y => decide (cntP (CF7 (cOf (swap 0 1 * swap 1 2))) y = 96 ∨
        cntP (CF7 (cOf (swap 0 1 * swap 1 2))) y = 48)) fun b y hb => ?_).trans h5
      rw [ccardB_eq_cntP hF hb]
    exact fun b hb => of_decide_eq_true (List.all_eq_true.1 e b hb)
  · have e : (CYL g0).all (fun b => decide (ccardB g0 b = 12)) = true := by
      refine (f2_all hYg (Q := fun y =>
        decide (cntP (CF7 (cOf (swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)))) y = 12))
        fun b y hb => ?_).trans h6
      rw [ccardB_eq_cntP hG hb]
    exact fun b hb => of_decide_eq_true (List.all_eq_true.1 e b hb)

end CertificateChecks.Batch5077

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.FF in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5077 : (∀ p ∈ PL, (p.1 * p.2) ^ 12 = 1)
    ∧ (PL.countP (fun p => powB 12 (p.1 * p.2) x0F) = 27)
    ∧ ((CYL f0).countP (fun b => decide (ccardB f0 b = 96)) = 3)
    ∧ ((CYL f0).countP (fun b => decide (ccardB f0 b = 48)) = 6)
    ∧ (∀ b ∈ CYL f0, ccardB f0 b = 96 ∨ ccardB f0 b = 48)
    ∧ (∀ b ∈ CYL g0, ccardB g0 b = 12) := CertificateChecks.Batch5077.facts

end Certificates
