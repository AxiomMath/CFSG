module

public import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public import CFSG.GH74.GLS.C3.Layer2.L5FinInputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5FinInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5072

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem E5list_mul_chk_0 : E5list.all (fun a => E5list.all fun b => decide (a * b ∈ E5list)) = true := by
  decide +kernel

private theorem E5list_inv_chk_1 : E5list.all (fun a => decide (a⁻¹ ∈ E5list)) = true := by
  decide +kernel

private theorem E5list_T5_chk_2 : E5list.all T5b = true := by
  decide +kernel

private theorem E5_comm_chk_3 : E5list.all (fun a => E5list.all fun b => decide (a * b = b * a)) = true := by
  decide +kernel

private theorem E5_sq_chk_4 : E5list.all (fun a => decide (a * a = 1)) = true := by
  decide +kernel

private theorem E5list_nodup_5 : E5list.Nodup := by
  decide +kernel

private theorem T5_norm_E5_chk_6 : allT5.all (fun t => E5list.all fun e => decide (t * e * t⁻¹ ∈ E5list)) = true := by
  decide +kernel

private theorem centT_E5_chk_7 : allT5.all (fun t => imp (E5list.all fun e => decide (t * e = e * t)) (decide (t ∈ E5list))) =
      true := by
  decide +kernel

private theorem E5_char_chk_8 : allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ≠ 1))
    (decide ((u ∈ E5list ∧ u ≠ vhat5) ↔ (nmE u = 4 ∧ nmE (u * vhat5) = 4))))) = true := by
  decide +kernel

private theorem cent_vhat5_chk_9 : F5list.all (fun g => imp (decide (g * vhat5 = vhat5 * g)) (T5b g)) = true := by
  decide +kernel

private theorem T5_comm_vhat5_chk_10 : allT5.all (fun t => decide (t * vhat5 = vhat5 * t)) = true := by
  decide +kernel

private theorem sigma5_chk_11 : allT5.all (fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
    (imp (decide (nmE s = 8)) (imp (decide (nmE (f1 * s) = 4))
      (F5list.any fun g => decide (g * s * g⁻¹ = vhat5)))))) = true := by
  decide +kernel

private theorem nmE_vhat5_12 : nmE vhat5 = 8 := by
  decide +kernel

private theorem vhat5_sq_13 : vhat5 * vhat5 = 1 := by
  decide +kernel

private theorem vhat5_ne_one_14 : vhat5 ≠ 1 := by
  decide +kernel

private theorem S0_inv_chk_15 : S0l.all (fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
    (imp (decide (s ∉ R5list)) (decide (numMoved s = 8))))) = true := by
  decide +kernel

private theorem Z_S0_chk_16 : S0l.all (fun s => imp (S0l.all fun t => decide (s * t = t * s))
    (decide (s = 1 ∨ s = yS))) = true := by
  decide +kernel

private theorem yS_sq_17 : yS * yS = 1 := by
  decide +kernel

private theorem yS_ne_one_18 : yS ≠ 1 := by
  decide +kernel

private theorem numMoved_yS_19 : numMoved yS = 8 := by
  decide +kernel

private theorem yS_central_chk_20 : S0l.all (fun t => decide (t * yS = yS * t)) = true := by
  decide +kernel

private theorem E9_comm_chk_21 : E9l.all (fun a => E9l.all fun b => decide (a * b = b * a)) = true := by
  decide +kernel

private theorem E9_sq_chk_22 : E9l.all (fun a => decide (a * a = 1)) = true := by
  decide +kernel

private theorem S0_norm_E9_chk_23 : S0l.all (fun s => E9l.all fun e => decide (s * e * s⁻¹ ∈ E9l)) = true := by
  decide +kernel

private theorem E9_char_chk_24 : S0l.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ≠ 1))
    (decide ((u ∈ E9l ∧ u ≠ yS) ↔ (numMoved u = 4 ∧ numMoved (u * yS) = 4))))) = true := by
  decide +kernel

private theorem Rc9list_mul_chk_25 : Rc9list.all (fun a => Rc9list.all fun b => decide (a * b ∈ Rc9list)) = true := by
  decide +kernel

private theorem Rc9list_inv_chk_26 : Rc9list.all (fun a => decide (a⁻¹ ∈ Rc9list)) = true := by
  decide +kernel

private theorem Rc9list_S0_chk_27 : Rc9list.all (fun p => decide (p ∈ S0l)) = true := by
  decide +kernel

private theorem Rc9_inter_chk_28 : Rc9list.all (fun r => imp (decide (r ∈ E9l)) (decide (r = 1))) = true := by
  decide +kernel

private theorem S0_split_chk_29 : S0l.all (fun s => E9l.any fun e => Rc9list.any fun r =>
    decide (s = e * r)) = true := by
  decide +kernel

end CertificateChecks.Batch5072

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5072 : (E5list.all (fun a => E5list.all fun b => decide (a * b ∈ E5list)) = true)
    ∧ (E5list.all (fun a => decide (a⁻¹ ∈ E5list)) = true)
    ∧ (E5list.all T5b = true)
    ∧ (E5list.all (fun a => E5list.all fun b => decide (a * b = b * a)) = true)
    ∧ (E5list.all (fun a => decide (a * a = 1)) = true)
    ∧ (E5list.Nodup)
    ∧ (allT5.all (fun t => E5list.all fun e => decide (t * e * t⁻¹ ∈ E5list)) = true)
    ∧ (allT5.all (fun t => imp (E5list.all fun e => decide (t * e = e * t)) (decide (t ∈ E5list))) =
      true)
    ∧ (allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ≠ 1))
    (decide ((u ∈ E5list ∧ u ≠ vhat5) ↔ (nmE u = 4 ∧ nmE (u * vhat5) = 4))))) = true)
    ∧ (F5list.all (fun g => imp (decide (g * vhat5 = vhat5 * g)) (T5b g)) = true)
    ∧ (allT5.all (fun t => decide (t * vhat5 = vhat5 * t)) = true)
    ∧ (allT5.all (fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
    (imp (decide (nmE s = 8)) (imp (decide (nmE (f1 * s) = 4))
      (F5list.any fun g => decide (g * s * g⁻¹ = vhat5)))))) = true)
    ∧ (nmE vhat5 = 8)
    ∧ (vhat5 * vhat5 = 1)
    ∧ (vhat5 ≠ 1)
    ∧ (S0l.all (fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
    (imp (decide (s ∉ R5list)) (decide (numMoved s = 8))))) = true)
    ∧ (S0l.all (fun s => imp (S0l.all fun t => decide (s * t = t * s))
    (decide (s = 1 ∨ s = yS))) = true)
    ∧ (yS * yS = 1)
    ∧ (yS ≠ 1)
    ∧ (numMoved yS = 8)
    ∧ (S0l.all (fun t => decide (t * yS = yS * t)) = true)
    ∧ (E9l.all (fun a => E9l.all fun b => decide (a * b = b * a)) = true)
    ∧ (E9l.all (fun a => decide (a * a = 1)) = true)
    ∧ (S0l.all (fun s => E9l.all fun e => decide (s * e * s⁻¹ ∈ E9l)) = true)
    ∧ (S0l.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ≠ 1))
    (decide ((u ∈ E9l ∧ u ≠ yS) ↔ (numMoved u = 4 ∧ numMoved (u * yS) = 4))))) = true)
    ∧ (Rc9list.all (fun a => Rc9list.all fun b => decide (a * b ∈ Rc9list)) = true)
    ∧ (Rc9list.all (fun a => decide (a⁻¹ ∈ Rc9list)) = true)
    ∧ (Rc9list.all (fun p => decide (p ∈ S0l)) = true)
    ∧ (Rc9list.all (fun r => imp (decide (r ∈ E9l)) (decide (r = 1))) = true)
    ∧ (S0l.all (fun s => E9l.any fun e => Rc9list.any fun r =>
    decide (s = e * r)) = true) := by
  exact ⟨CertificateChecks.Batch5072.E5list_mul_chk_0, CertificateChecks.Batch5072.E5list_inv_chk_1, CertificateChecks.Batch5072.E5list_T5_chk_2, CertificateChecks.Batch5072.E5_comm_chk_3, CertificateChecks.Batch5072.E5_sq_chk_4, CertificateChecks.Batch5072.E5list_nodup_5, CertificateChecks.Batch5072.T5_norm_E5_chk_6, CertificateChecks.Batch5072.centT_E5_chk_7, CertificateChecks.Batch5072.E5_char_chk_8, CertificateChecks.Batch5072.cent_vhat5_chk_9, CertificateChecks.Batch5072.T5_comm_vhat5_chk_10, CertificateChecks.Batch5072.sigma5_chk_11, CertificateChecks.Batch5072.nmE_vhat5_12, CertificateChecks.Batch5072.vhat5_sq_13, CertificateChecks.Batch5072.vhat5_ne_one_14, CertificateChecks.Batch5072.S0_inv_chk_15, CertificateChecks.Batch5072.Z_S0_chk_16, CertificateChecks.Batch5072.yS_sq_17, CertificateChecks.Batch5072.yS_ne_one_18, CertificateChecks.Batch5072.numMoved_yS_19, CertificateChecks.Batch5072.yS_central_chk_20, CertificateChecks.Batch5072.E9_comm_chk_21, CertificateChecks.Batch5072.E9_sq_chk_22, CertificateChecks.Batch5072.S0_norm_E9_chk_23, CertificateChecks.Batch5072.E9_char_chk_24, CertificateChecks.Batch5072.Rc9list_mul_chk_25, CertificateChecks.Batch5072.Rc9list_inv_chk_26, CertificateChecks.Batch5072.Rc9list_S0_chk_27, CertificateChecks.Batch5072.Rc9_inter_chk_28, CertificateChecks.Batch5072.S0_split_chk_29⟩

end Certificates
