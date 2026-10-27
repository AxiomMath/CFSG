
module

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

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5045

set_option maxRecDepth 100000

private theorem Pml_mul_chk_0 : mulClosedChk Pml = true := by
  decide +kernel

private theorem Pml_inv_chk_1 : invClosedChk Pml = true := by
  decide +kernel

private theorem Qml_mul_chk_2 : mulClosedChk Qml = true := by
  decide +kernel

private theorem Qml_inv_chk_3 : invClosedChk Qml = true := by
  decide +kernel

private theorem Rml_mul_chk_4 : mulClosedChk Rml = true := by
  decide +kernel

private theorem Rml_inv_chk_5 : invClosedChk Rml = true := by
  decide +kernel

private theorem one_mem_Rml_6 : (1 : Amb 5) ∈ Rml := by
  decide +kernel

private theorem Pml_nodup_7 : Pml.Nodup := by
  decide +kernel

private theorem Qml_nodup_8 : Qml.Nodup := by
  decide +kernel

private theorem Rml_nodup_9 : Rml.Nodup := by
  decide +kernel

private theorem Pml_sub_chk_10 : Pml.all (fun p => decide (p ∈ Rml)) = true := by
  decide +kernel

private theorem Qml_sub_chk_11 : Qml.all (fun p => decide (p ∈ Rml)) = true := by
  decide +kernel

private theorem Rml_prod_chk_12 : Rml.all (fun r => Pml.any fun p => Qml.any fun q => decide (r = p * q)) =
    true := by
  decide +kernel

private theorem Pml_Qml_chk_13 : Pml.all (fun p => imp (decide (p ∈ Qml)) (decide (p = 1))) = true := by
  decide +kernel

private theorem Rml_comm_chk_14 : Rml.all (fun a => Rml.all fun b => decide (a * b = b * a)) = true := by
  decide +kernel

private theorem Rml_sq_chk_15 : Rml.all (fun a => decide (a * a = 1)) = true := by
  decide +kernel

private theorem Rml_T5_chk_16 : Rml.all T5b = true := by
  decide +kernel

private theorem wm_mem_Km_17 : wm ∈ Km := by
  rw [mem_Km]
  exact ⟨rfl, by decide +kernel⟩

private theorem wm_cube_18 : wm * wm * wm = 1 := by
  decide +kernel

private theorem wm_ne_one_19 : wm ≠ 1 := by
  decide +kernel

private theorem wm_comm_Q_chk_20 : Qml.all (fun q => decide (wm * q = q * wm)) = true := by
  decide +kernel

private theorem wm_norm_P_chk_21 : Pml.all (fun p => decide (wm * p * wm⁻¹ ∈ Pml)) = true := by
  decide +kernel

private theorem wm_free_chk_22 : Pml.all (fun p => imp (decide (p ≠ 1)) (decide (wm * p * wm⁻¹ ≠ p))) = true := by
  decide +kernel

private theorem wm_norm_R_chk_23 : Rml.all (fun r => decide (wm * r * wm⁻¹ ∈ Rml)) = true := by
  decide +kernel

private theorem Qm_coord_chk_24 : allT5.all (fun g => decide (g.1 = 1 ↔ g ∈ Qml)) = true := by
  decide +kernel

private theorem Pm_coord_chk_25 : allT5.all (fun g => decide (g.2 = 1 ↔ g ∈ Pml)) = true := by
  decide +kernel

private theorem FIN1_chk_26 : Rml.all (fun u => Rml.all fun v => imp (decide (u ≠ 1)) (imp (decide (v ≠ 1))
    (imp (decide (u ≠ v)) (imp (decide (wm * u * wm⁻¹ ∈ [u, v, u * v] ∧
      wm * v * wm⁻¹ ∈ [u, v, u * v])) (decide ((u ∈ Pml ∧ v ∈ Pml) ∨ (u ∈ Qml ∧ v ∈ Qml))))))) =
    true := by
  decide +kernel

private theorem FIN2_chk_27 : Rml.all (fun u => Rml.all fun v => imp (decide (u ≠ 1)) (imp (decide (v ≠ 1))
    (imp (decide (u ≠ v)) (imp (decide (u ∉ Qml ∧ v ∉ Qml ∧ u * v ∉ Qml))
      (imp (decide (u ∈ Pml ∨ v ∈ Pml ∨ u * v ∈ Pml))
        (decide (wm * u * wm⁻¹ ∈ [u, v, u * v] ∨ wm * v * wm⁻¹ ∈ [u, v, u * v] ∨
          wm * (u * v) * wm⁻¹ ∈ [u, v, u * v]))))))) = true := by
  decide +kernel

private theorem centRm_chk_28 : F5list.all (fun g => imp (Rml.all fun r => decide (g * r = r * g))
    (decide (g ∈ Rml))) = true := by
  decide +kernel

private theorem T5_cent_le_chk_29 : allT5.all (fun t => imp (decide (t ∉ Rml))
    (decide ((allT5.filter (fun s => decide (s * t = t * s))).length ≤ 8))) = true := by
  decide +kernel

private theorem T5_norm_Rm_chk_30 : allT5.all (fun t => Rml.all fun r => decide (t * r * t⁻¹ ∈ Rml)) =
    true := by
  decide +kernel

private theorem V4_cent_chk_31 : (g5Perms 4).all (fun τ => imp (decide (τ * x4 = x4 * τ))
    (imp (decide (τ * y4 = y4 * τ)) (decide (τ ∈ V4l)))) = true := by
  decide +kernel

private theorem V4_even_chk_32 : V4l.all (fun τ => decide (sign τ = 1)) = true := by
  decide +kernel

end CertificateChecks.Batch5045

namespace Certificates

end Certificates
