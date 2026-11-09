module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs
meta import Mathlib.Algebra.Group.End
meta import Mathlib.GroupTheory.Perm.Sign
meta import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.GroupTheory.Perm.Fin
meta import Mathlib.Logic.Equiv.Fin.Basic
meta import Mathlib.Logic.Equiv.Option
meta import Mathlib.Data.List.FinRange
meta import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open CFSG.GH74.GLS.C3.Prop121.Card7
open CFSG.GH74.GLS.C3.Prop121.Card7.HC
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

namespace CertificateChecks.Batch5080

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open CFSG.GH74.GLS.C3.Prop121.Card7
open CFSG.GH74.GLS.C3.Prop121.Card7.HC
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem flatMap_eq_prod {α β γ δ : Type*} (L1 : List α) (L2 : List β) (L3 : List γ)
    (g : α → β → γ → δ) :
    (L1.flatMap fun a => L2.flatMap fun b => L3.map fun c => g a b c) =
      (L1 ×ˢ (L2 ×ˢ L3)).map (fun p => g p.1 p.2.1 p.2.2) := by
  induction L1 with
  | nil => rfl
  | cons a L1 ih =>
    rw [List.flatMap_cons, List.product_cons, List.map_append, ih, List.map_map]
    congr 1
    clear ih
    induction L2 with
    | nil => rfl
    | cons b L2 ih2 =>
      rw [List.flatMap_cons, List.product_cons, List.map_append, ← ih2, List.map_map]
      rfl

private theorem H0_eq_map :
    H0 = (flipsL ×ˢ (s4L ×ˢ s3L)).map (fun p => p.1 * p.2.1 * p.2.2) :=
  flatMap_eq_prod _ _ _ fun f s t => f * s * t

private theorem countP_sign_triple (L1 L2 L3 : List P11) :
    (L1.flatMap fun f => L2.flatMap fun s => L3.map fun t => f * s * t).countP
        (fun σ => decide (sign σ = 1)) =
      ((L1.map sign).flatMap fun a => (L2.map sign).flatMap fun b =>
        (L3.map sign).map fun c => a * b * c).countP (fun u => decide (u = 1)) := by
  simp [List.countP_flatMap, List.countP_map, List.flatMap_map, Function.comp_def]

private theorem flipsL_sign : flipsL.map sign =
    [1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1] := by
  decide +kernel

private theorem s4L_sign : s4L.map sign = List.replicate 24 1 := by
  decide +kernel

private theorem s3L_sign : s3L.map sign = [1, -1, 1, -1, -1, 1] := by
  decide +kernel

private theorem HL_len_true_0 : decide (HL.length = 1152) = true := by
  apply decide_eq_true
  rw [HL, ← List.countP_eq_length_filter, H0, countP_sign_triple, flipsL_sign, s4L_sign,
    s3L_sign]
  decide +kernel

private theorem flipsL_comm : flipsL.all (fun f => decide (f * Y11 = Y11 * f)) = true := by
  decide +kernel

private theorem s4L_comm : s4L.all (fun f => decide (f * Y11 = Y11 * f)) = true := by
  decide +kernel

private theorem s3L_comm : s3L.all (fun f => decide (f * Y11 = Y11 * f)) = true := by
  decide +kernel

private theorem hp_of_mem_HL (σ : P11) (hσ : σ ∈ HL) : Hp σ := by
  rw [HL, List.mem_filter, H0_eq_map, List.mem_map] at hσ
  obtain ⟨⟨⟨f, s, t⟩, hm, rfl⟩, hsg⟩ := hσ
  simp only [List.mem_product] at hm
  have hf : f * Y11 = Y11 * f := of_decide_eq_true (List.all_eq_true.1 flipsL_comm f hm.1)
  have hs : s * Y11 = Y11 * s := of_decide_eq_true (List.all_eq_true.1 s4L_comm s hm.2.1)
  have ht : t * Y11 = Y11 * t := of_decide_eq_true (List.all_eq_true.1 s3L_comm t hm.2.2)
  exact ⟨of_decide_eq_true hsg,
    ((Commute.mul_left (a := f) (b := s) hf hs).mul_left (b := t) ht).eq⟩

private theorem HL_hp_true_2 : (HL.all fun σ => decide (Hp σ)) = true :=
  List.all_eq_true.2 fun σ hσ => decide_eq_true (hp_of_mem_HL σ hσ)

private def key3 (σ : P11) : ℕ := (σ 8).val * 121 + (σ 9).val * 11 + (σ 10).val

private def key4 (σ : P11) : ℕ :=
  (σ 0).val / 2 * 64 + (σ 2).val / 2 * 16 + (σ 4).val / 2 * 4 + (σ 6).val / 2

private theorem flipsL_fix : flipsL.all (fun f => (List.finRange 11).all fun x =>
    decide (8 ≤ x.val → f x = x)) = true := by
  decide +kernel

private theorem s4L_fix : s4L.all (fun f => (List.finRange 11).all fun x =>
    decide (8 ≤ x.val → f x = x)) = true := by
  decide +kernel

private theorem s3L_high : s3L.all (fun t =>
    decide (8 ≤ (t 8).val ∧ 8 ≤ (t 9).val ∧ 8 ≤ (t 10).val)) = true := by
  decide +kernel

private theorem flipsL_half : flipsL.all (fun f => (List.finRange 11).all fun x =>
    decide ((f x).val / 2 = x.val / 2)) = true := by
  decide +kernel

private theorem key3_nodup : (s3L.map key3).Nodup := by
  decide +kernel

private theorem key4_nodup : (s4L.map key4).Nodup := by
  decide +kernel

private theorem flipsL_nodup : flipsL.Nodup := by
  decide +kernel

private theorem s4L_nodup : s4L.Nodup := by
  decide +kernel

private theorem s3L_nodup : s3L.Nodup := by
  decide +kernel

private theorem fix_high {L : List P11}
    (h : L.all (fun f => (List.finRange 11).all fun x => decide (8 ≤ x.val → f x = x)) = true)
    {f : P11} (hf : f ∈ L) (x : Fin 11) (hx : 8 ≤ x.val) : f x = x :=
  of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h f hf) x (List.mem_finRange x)) hx

private theorem key3_mul (f s t : P11) (hf : f ∈ flipsL) (hs : s ∈ s4L) (ht : t ∈ s3L) :
    key3 (f * s * t) = key3 t := by
  obtain ⟨h8, h9, h10⟩ := of_decide_eq_true (List.all_eq_true.1 s3L_high t ht)
  simp only [key3, Perm.mul_apply, fix_high s4L_fix hs _ h8, fix_high s4L_fix hs _ h9,
    fix_high s4L_fix hs _ h10, fix_high flipsL_fix hf _ h8, fix_high flipsL_fix hf _ h9,
    fix_high flipsL_fix hf _ h10]

private theorem key4_mul (f s : P11) (hf : f ∈ flipsL) : key4 (f * s) = key4 s := by
  have h x : (f x).val / 2 = x.val / 2 :=
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 flipsL_half f hf) x
      (List.mem_finRange x))
  simp only [key4, Perm.mul_apply, h]

private theorem H0_nodup : H0.Nodup := by
  rw [H0_eq_map]
  refine (flipsL_nodup.product (s4L_nodup.product s3L_nodup)).map_on ?_
  rintro ⟨f, s, t⟩ hx ⟨f', s', t'⟩ hy h
  simp only [List.mem_product] at hx hy
  obtain ⟨hf, hs, ht⟩ := hx
  obtain ⟨hf', hs', ht'⟩ := hy
  have htt : t = t' := List.inj_on_of_nodup_map key3_nodup ht ht' (by
    rw [← key3_mul f s t hf hs ht, ← key3_mul f' s' t' hf' hs' ht']
    exact congrArg key3 h)
  subst htt
  have h1 : f * s = f' * s' := mul_right_cancel h
  have hss : s = s' := List.inj_on_of_nodup_map key4_nodup hs hs' (by
    rw [← key4_mul f s hf, ← key4_mul f' s' hf']
    exact congrArg key4 h1)
  subst hss
  rw [mul_right_cancel h1]

private theorem HL_nodup_true_1 : decide HL.Nodup = true :=
  decide_eq_true (H0_nodup.filter _)

end CertificateChecks.Batch5080

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.HC in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3 in
theorem certificate5080 : (decide (HL.length = 1152) = true)
    ∧ (decide HL.Nodup = true)
    ∧ ((HL.all fun σ => decide (Hp σ)) = true) := by
  exact ⟨CertificateChecks.Batch5080.HL_len_true_0, CertificateChecks.Batch5080.HL_nodup_true_1, CertificateChecks.Batch5080.HL_hp_true_2⟩

end Certificates
