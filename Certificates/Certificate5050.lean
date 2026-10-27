module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public import CFSG.GH74.GLS.C3.Layer2.L5B5Inputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B5Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5050

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem T5_pow4_chk_0 : allT5.all (fun t => decide (t * t * (t * t) = 1)) = true := by
  decide +kernel

private theorem T5_sq_mem_R_chk_1 : allT5.all (fun t => decide (t * t ∈ Rml)) = true := by
  decide +kernel

private theorem T5_cent_Z_chk_2 : allT5.all (fun z => imp (allT5.all fun t => decide (z * t = t * z))
    (decide (z ∈ ZTl))) = true := by
  decide +kernel

private theorem ZTl_central_chk_3 : ZTl.all (fun z => allT5.all fun t => decide (z * t = t * z)) = true := by
  decide +kernel

private theorem ZTl_P_chk_4 : Pml.all (fun p => imp (decide (p ∈ ZTl)) (decide (p = 1 ∨ p = e1))) = true := by
  decide +kernel

private theorem ZTl_sq_chk_5 : ZTl.all (fun z => decide (z * z = 1)) = true := by
  decide +kernel

private theorem ZTl_le_R_chk_6 : ZTl.all (fun z => decide (z ∈ Rml)) = true := by
  decide +kernel

private theorem T5_cent_invol_Z_chk_7 : allT5.all (fun t => imp (decide (t * t ≠ 1))
    (allT5.all fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
      (imp (decide (s * t = t * s)) (decide (s ∈ ZTl)))))) = true := by
  decide +kernel

private theorem T5_JR_conj_chk_8 : allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ∉ Rml))
    (allT5.all fun t => imp (decide (t * t = 1)) (imp (decide (t ∉ Rml))
      (Rml.any fun r => decide (r * u * r⁻¹ = t)))))) = true := by
  decide +kernel

private theorem T5_JR_prod_Z_chk_9 : allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ∉ Rml))
    (allT5.all fun t => imp (decide (t * t = 1)) (imp (decide (t ∉ Rml))
      (decide (u * t ∈ ZTl)))))) = true := by
  decide +kernel

private theorem T5_conj_P_chk_10 : allT5.all (fun y => imp (decide (y * y = 1)) (imp (decide (y ∉ Rml))
    (Pml.all fun p => imp (decide (p ≠ 1 ∧ p ≠ e1)) (decide (y * p * y⁻¹ = p * e1))))) = true := by
  decide +kernel

private theorem fz_chk_11 : allT5.all (fun t1 => imp (decide (t1 * t1 = f1)) (allT5.all fun X =>
    imp (decide (X * X = 1)) (imp (!mixb X) (Rml.all fun V => imp (mixb V)
      (decide (t1 * X * t1⁻¹ ≠ X * V)))))) = true := by
  decide +kernel

private theorem four_F_chk_12 : Rml.all (fun a => Rml.all fun b => Rml.all fun r =>
    imp (mixb a && mixb b && mixb (a * b) && decide (r ≠ 1) && !mixb r)
      (mixb (r * a) || mixb (r * b) || mixb (r * (a * b)))) = true := by
  decide +kernel

private theorem e1_mem_Pm_check_13 : e1 ∈ Pml := by
  decide +kernel

private theorem f1_mem_Qm_check_14 : f1 ∈ Qml := by
  decide +kernel

end CertificateChecks.Batch5050

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5050 : (allT5.all (fun t => decide (t * t * (t * t) = 1)) = true)
    ∧ (allT5.all (fun t => decide (t * t ∈ Rml)) = true)
    ∧ (allT5.all (fun z => imp (allT5.all fun t => decide (z * t = t * z))
    (decide (z ∈ ZTl))) = true)
    ∧ (ZTl.all (fun z => allT5.all fun t => decide (z * t = t * z)) = true)
    ∧ (Pml.all (fun p => imp (decide (p ∈ ZTl)) (decide (p = 1 ∨ p = e1))) = true)
    ∧ (ZTl.all (fun z => decide (z * z = 1)) = true)
    ∧ (ZTl.all (fun z => decide (z ∈ Rml)) = true)
    ∧ (allT5.all (fun t => imp (decide (t * t ≠ 1))
    (allT5.all fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
      (imp (decide (s * t = t * s)) (decide (s ∈ ZTl)))))) = true)
    ∧ (allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ∉ Rml))
    (allT5.all fun t => imp (decide (t * t = 1)) (imp (decide (t ∉ Rml))
      (Rml.any fun r => decide (r * u * r⁻¹ = t)))))) = true)
    ∧ (allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ∉ Rml))
    (allT5.all fun t => imp (decide (t * t = 1)) (imp (decide (t ∉ Rml))
      (decide (u * t ∈ ZTl)))))) = true)
    ∧ (allT5.all (fun y => imp (decide (y * y = 1)) (imp (decide (y ∉ Rml))
    (Pml.all fun p => imp (decide (p ≠ 1 ∧ p ≠ e1)) (decide (y * p * y⁻¹ = p * e1))))) = true)
    ∧ (allT5.all (fun t1 => imp (decide (t1 * t1 = f1)) (allT5.all fun X =>
    imp (decide (X * X = 1)) (imp (!mixb X) (Rml.all fun V => imp (mixb V)
      (decide (t1 * X * t1⁻¹ ≠ X * V)))))) = true)
    ∧ (Rml.all (fun a => Rml.all fun b => Rml.all fun r =>
    imp (mixb a && mixb b && mixb (a * b) && decide (r ≠ 1) && !mixb r)
      (mixb (r * a) || mixb (r * b) || mixb (r * (a * b)))) = true)
    ∧ (e1 ∈ Pml)
    ∧ (f1 ∈ Qml) := by
  exact ⟨CertificateChecks.Batch5050.T5_pow4_chk_0, CertificateChecks.Batch5050.T5_sq_mem_R_chk_1, CertificateChecks.Batch5050.T5_cent_Z_chk_2, CertificateChecks.Batch5050.ZTl_central_chk_3, CertificateChecks.Batch5050.ZTl_P_chk_4, CertificateChecks.Batch5050.ZTl_sq_chk_5, CertificateChecks.Batch5050.ZTl_le_R_chk_6, CertificateChecks.Batch5050.T5_cent_invol_Z_chk_7, CertificateChecks.Batch5050.T5_JR_conj_chk_8, CertificateChecks.Batch5050.T5_JR_prod_Z_chk_9, CertificateChecks.Batch5050.T5_conj_P_chk_10, CertificateChecks.Batch5050.fz_chk_11, CertificateChecks.Batch5050.four_F_chk_12, CertificateChecks.Batch5050.e1_mem_Pm_check_13, CertificateChecks.Batch5050.f1_mem_Qm_check_14⟩

end Certificates
