module

public import CFSG.GH74.GLS.C3.Prop121.Card7F5Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

namespace C5079

open CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def qT (t : Amb 7) : Bool :=
  decide ((t.2 * x4 = x4 * t.2 ∧ sign t.1 = sign t.2) ∧ (t ^ 2 = 1 ∧ t ≠ 1) ∧ nm7 t = 4)

theorem cnt_ok : Nat.beq ((Tl 7).countP qT) 14 = true := by quickRfl

theorem xf_iff (s : F7) :
    XF s ↔ ((s : Amb 7) ^ 2 = 1 ∧ (s : Amb 7) ≠ 1) ∧ nm7 (s : Amb 7) = 4 := by
  have e1 : s ^ 2 = 1 ↔ (s : Amb 7) ^ 2 = 1 :=
    ⟨fun h => by rw [← Subgroup.coe_pow, h, Subgroup.coe_one],
      fun h => Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])⟩
  have e2 : s ≠ 1 ↔ (s : Amb 7) ≠ 1 :=
    not_congr ⟨fun h => by rw [h, Subgroup.coe_one],
      fun h => Subtype.ext (by rw [h, Subgroup.coe_one])⟩
  unfold XF IsInv
  rw [e1, e2]

theorem mem_XAll' {s : F7} : s ∈ XAll ↔ XF s := by simp [XAll, mem_F7L]

@[expose] def tlEquiv : {x : F7 // XF x ∧ (x : Amb 7) ∈ Tl 7} ≃
    {t : Amb 7 // t ∈ Tl 7 ∧ ((t.2 * x4 = x4 * t.2 ∧ sign t.1 = sign t.2) ∧
      (t ^ 2 = 1 ∧ t ≠ 1) ∧ nm7 t = 4)} where
  toFun x := ⟨x.1.1, x.2.2, x.1.2, (xf_iff x.1).1 x.2.1⟩
  invFun t := ⟨⟨t.1, t.2.2.1⟩, (xf_iff ⟨t.1, t.2.2.1⟩).2 t.2.2.2, t.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_eq : XAll.countP (fun s : F7 => decide ((s : Amb 7) ∈ Tl 7)) = (Tl 7).countP qT := by
  have hX := card_subtype_eq_countP XAll (F7L_nodup.filter _)
    (fun x : F7 => XF x ∧ (x : Amb 7) ∈ Tl 7) (fun s : F7 => decide ((s : Amb 7) ∈ Tl 7))
    (fun x => by rw [mem_XAll', decide_eq_true_eq])
  have hT := card_subtype_eq_countP (Tl 7) (Tl_facts 7 (Or.inr rfl)).2.1
    (fun t : Amb 7 => t ∈ Tl 7 ∧ ((t.2 * x4 = x4 * t.2 ∧ sign t.1 = sign t.2) ∧
      (t ^ 2 = 1 ∧ t ≠ 1) ∧ nm7 t = 4)) qT
    (fun t => by rw [qT, decide_eq_true_eq])
  exact hX.symm.trans ((Nat.card_congr tlEquiv).trans hT)

end C5079

open Certificates in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.FF in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem check5079 : XAll.countP (fun s : F7 => decide ((s : Amb 7) ∈ Tl 7)) = 14 :=
  C5079.count_eq.trans (Nat.eq_of_beq_eq_true C5079.cnt_ok)

end CertificateChecks.KernelCensus
