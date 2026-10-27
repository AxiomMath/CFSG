
module

public import Certificates.Certificate5045Base
import all Certificates.Certificate5045Base

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
import CFSG.GH74.GLS.C3.Layer2.L5A1Base

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5045

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

end CertificateChecks.Batch5045

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5045 : (mulClosedChk Pml = true)
    ∧ (invClosedChk Pml = true)
    ∧ (mulClosedChk Qml = true)
    ∧ (invClosedChk Qml = true)
    ∧ (mulClosedChk Rml = true)
    ∧ (invClosedChk Rml = true)
    ∧ ((1 : Amb 5) ∈ Rml)
    ∧ (Pml.Nodup)
    ∧ (Qml.Nodup)
    ∧ (Rml.Nodup)
    ∧ (Pml.all (fun p => decide (p ∈ Rml)) = true)
    ∧ (Qml.all (fun p => decide (p ∈ Rml)) = true)
    ∧ (Rml.all (fun r => Pml.any fun p => Qml.any fun q => decide (r = p * q)) =
    true)
    ∧ (Pml.all (fun p => imp (decide (p ∈ Qml)) (decide (p = 1))) = true)
    ∧ (Rml.all (fun a => Rml.all fun b => decide (a * b = b * a)) = true)
    ∧ (Rml.all (fun a => decide (a * a = 1)) = true)
    ∧ (Rml.all T5b = true)
    ∧ (wm ∈ Km)
    ∧ (wm * wm * wm = 1)
    ∧ (wm ≠ 1)
    ∧ (Qml.all (fun q => decide (wm * q = q * wm)) = true)
    ∧ (Pml.all (fun p => decide (wm * p * wm⁻¹ ∈ Pml)) = true)
    ∧ (Pml.all (fun p => imp (decide (p ≠ 1)) (decide (wm * p * wm⁻¹ ≠ p))) = true)
    ∧ (Rml.all (fun r => decide (wm * r * wm⁻¹ ∈ Rml)) = true)
    ∧ (allT5.all (fun g => decide (g.1 = 1 ↔ g ∈ Qml)) = true)
    ∧ (allT5.all (fun g => decide (g.2 = 1 ↔ g ∈ Pml)) = true)
    ∧ (Rml.all (fun u => Rml.all fun v => imp (decide (u ≠ 1)) (imp (decide (v ≠ 1))
    (imp (decide (u ≠ v)) (imp (decide (wm * u * wm⁻¹ ∈ [u, v, u * v] ∧
      wm * v * wm⁻¹ ∈ [u, v, u * v])) (decide ((u ∈ Pml ∧ v ∈ Pml) ∨ (u ∈ Qml ∧ v ∈ Qml))))))) =
    true)
    ∧ (Rml.all (fun u => Rml.all fun v => imp (decide (u ≠ 1)) (imp (decide (v ≠ 1))
    (imp (decide (u ≠ v)) (imp (decide (u ∉ Qml ∧ v ∉ Qml ∧ u * v ∉ Qml))
      (imp (decide (u ∈ Pml ∨ v ∈ Pml ∨ u * v ∈ Pml))
        (decide (wm * u * wm⁻¹ ∈ [u, v, u * v] ∨ wm * v * wm⁻¹ ∈ [u, v, u * v] ∨
          wm * (u * v) * wm⁻¹ ∈ [u, v, u * v]))))))) = true)
    ∧ (F5list.all (fun g => imp (Rml.all fun r => decide (g * r = r * g))
    (decide (g ∈ Rml))) = true)
    ∧ (allT5.all (fun t => imp (decide (t ∉ Rml))
    (decide ((allT5.filter (fun s => decide (s * t = t * s))).length ≤ 8))) = true)
    ∧ (allT5.all (fun t => Rml.all fun r => decide (t * r * t⁻¹ ∈ Rml)) =
    true)
    ∧ ((g5Perms 4).all (fun τ => imp (decide (τ * x4 = x4 * τ))
    (imp (decide (τ * y4 = y4 * τ)) (decide (τ ∈ V4l)))) = true)
    ∧ (V4l.all (fun τ => decide (sign τ = 1)) = true) := by
  exact ⟨CertificateChecks.Batch5045.Pml_mul_chk_0, CertificateChecks.Batch5045.Pml_inv_chk_1, CertificateChecks.Batch5045.Qml_mul_chk_2, CertificateChecks.Batch5045.Qml_inv_chk_3, CertificateChecks.Batch5045.Rml_mul_chk_4, CertificateChecks.Batch5045.Rml_inv_chk_5, CertificateChecks.Batch5045.one_mem_Rml_6, CertificateChecks.Batch5045.Pml_nodup_7, CertificateChecks.Batch5045.Qml_nodup_8, CertificateChecks.Batch5045.Rml_nodup_9, CertificateChecks.Batch5045.Pml_sub_chk_10, CertificateChecks.Batch5045.Qml_sub_chk_11, CertificateChecks.Batch5045.Rml_prod_chk_12, CertificateChecks.Batch5045.Pml_Qml_chk_13, CertificateChecks.Batch5045.Rml_comm_chk_14, CertificateChecks.Batch5045.Rml_sq_chk_15, CertificateChecks.Batch5045.Rml_T5_chk_16, CertificateChecks.Batch5045.wm_mem_Km_17, CertificateChecks.Batch5045.wm_cube_18, CertificateChecks.Batch5045.wm_ne_one_19, CertificateChecks.Batch5045.wm_comm_Q_chk_20, CertificateChecks.Batch5045.wm_norm_P_chk_21, CertificateChecks.Batch5045.wm_free_chk_22, CertificateChecks.Batch5045.wm_norm_R_chk_23, CertificateChecks.Batch5045.Qm_coord_chk_24, CertificateChecks.Batch5045.Pm_coord_chk_25, CertificateChecks.Batch5045.FIN1_chk_26, CertificateChecks.Batch5045.FIN2_chk_27, CertificateChecks.Batch5045.centRm_chk_28, CertificateChecks.Batch5045.T5_cent_le_chk_29, CertificateChecks.Batch5045.T5_norm_Rm_chk_30, CertificateChecks.Batch5045.V4_cent_chk_31, CertificateChecks.Batch5045.V4_even_chk_32⟩

end Certificates
