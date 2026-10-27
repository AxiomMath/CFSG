module

public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5C10Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5C11Inputs
public import Certificates.Data.A5
import CFSG.GH74.GLS.C3.Layer2.L5C10
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B2
meta import CFSG.GH74.GLS.C3.Layer2.L5C0
meta import CFSG.GH74.GLS.C3.Layer2.L5C10
meta import CFSG.GH74.GLS.C3.Layer2.L5C11Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5053

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem gTw_mul_self_0 : gTw * gTw = 1 := by
  decide +kernel

private theorem gTw_inv_1 : gTw⁻¹ = gTw := by
  decide +kernel

private theorem gTw_conj_F5_chk_2 : allAmb5.all (fun p => CFSG.GH74.GLS.C3.Layer2.L5.imp (F5b p) (F5b (gTw * p * gTw⁻¹))) = true := by
  decide +kernel

private theorem gTw_conj_T5_chk_3 : allAmb5.all (fun p => decide (T5b p = T5b (gTw * p * gTw⁻¹))) = true := by
  decide +kernel

private theorem gTw_x0_4 : gTw * x0 5 * gTw⁻¹ = x0 5 := by
  decide +kernel

private theorem gTw_wm_5 : gTw * wm * gTw⁻¹ = wm := by
  decide +kernel

private theorem gTw_el16_chk_6 : (List.finRange 16).all
    (fun i => decide (gTw * el16 (twG i) * gTw⁻¹ = el16 i)) = true := by
  decide +kernel

private theorem twG_twG_chk_7 : (List.finRange 16).all (fun i => decide (twG (twG i) = i)) = true := by
  decide +kernel

private theorem gTw_conj_Rml_chk_8 : Rml.all (fun p => decide (gTw * p * gTw⁻¹ ∈ Rml)) = true := by
  decide +kernel

private theorem gTw_conj_Pml_chk_9 : Pml.all (fun p => decide (gTw * p * gTw⁻¹ ∈ Pml)) = true := by
  decide +kernel

private theorem gTw_conj_Qml_chk_10 : Qml.all (fun p => decide (gTw * p * gTw⁻¹ ∈ Qml)) = true := by
  decide +kernel

private theorem fam1G_image_tw_11 : fam1G.image (fun V => V.image twG) = fam0G := by
  decide +kernel

private theorem fam0G_image_tw_12 : fam0G.image (fun V => V.image twG) = fam1G := by
  decide +kernel

end CertificateChecks.Batch5053

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5053 : (CFSG.GH74.GLS.C3.Layer2.L5.gTw * CFSG.GH74.GLS.C3.Layer2.L5.gTw = 1)
    ∧ (CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹ = CFSG.GH74.GLS.C3.Layer2.L5.gTw)
    ∧ (allAmb5.all (fun p => CFSG.GH74.GLS.C3.Layer2.L5.imp (F5b p) (F5b (CFSG.GH74.GLS.C3.Layer2.L5.gTw * p * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹))) = true)
    ∧ (allAmb5.all (fun p => decide (T5b p = T5b (CFSG.GH74.GLS.C3.Layer2.L5.gTw * p * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹))) = true)
    ∧ (CFSG.GH74.GLS.C3.Layer2.L5.gTw * x0 5 * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹ = x0 5)
    ∧ (CFSG.GH74.GLS.C3.Layer2.L5.gTw * wm * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹ = wm)
    ∧ ((List.finRange 16).all
    (fun i => decide (CFSG.GH74.GLS.C3.Layer2.L5.gTw * el16 (twG i) * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹ = el16 i)) = true)
    ∧ ((List.finRange 16).all (fun i => decide (twG (twG i) = i)) = true)
    ∧ (Rml.all (fun p => decide (CFSG.GH74.GLS.C3.Layer2.L5.gTw * p * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹ ∈ Rml)) = true)
    ∧ (Pml.all (fun p => decide (CFSG.GH74.GLS.C3.Layer2.L5.gTw * p * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹ ∈ Pml)) = true)
    ∧ (Qml.all (fun p => decide (CFSG.GH74.GLS.C3.Layer2.L5.gTw * p * CFSG.GH74.GLS.C3.Layer2.L5.gTw⁻¹ ∈ Qml)) = true)
    ∧ (fam1G.image (fun V => V.image twG) = fam0G)
    ∧ (fam0G.image (fun V => V.image twG) = fam1G) := by
  exact ⟨CertificateChecks.Batch5053.gTw_mul_self_0, CertificateChecks.Batch5053.gTw_inv_1, CertificateChecks.Batch5053.gTw_conj_F5_chk_2, CertificateChecks.Batch5053.gTw_conj_T5_chk_3, CertificateChecks.Batch5053.gTw_x0_4, CertificateChecks.Batch5053.gTw_wm_5, CertificateChecks.Batch5053.gTw_el16_chk_6, CertificateChecks.Batch5053.twG_twG_chk_7, CertificateChecks.Batch5053.gTw_conj_Rml_chk_8, CertificateChecks.Batch5053.gTw_conj_Pml_chk_9, CertificateChecks.Batch5053.gTw_conj_Qml_chk_10, CertificateChecks.Batch5053.fam1G_image_tw_11, CertificateChecks.Batch5053.fam0G_image_tw_12⟩

end Certificates
