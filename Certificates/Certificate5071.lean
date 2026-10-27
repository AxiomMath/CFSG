
module

public import Certificates.Certificate5071Base
import all Certificates.Certificate5071Base

import CFSG.Certificates.Kernel.L5.HFVSound

public section

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5H

namespace CertificateChecks.Batch5071

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5H

set_option maxRecDepth 100000

private theorem planes0_fam0_32 : ∀ V ∈ planes0, V.toFinset ∈ fam0 := planes0_fam0

private theorem fam0_planes0_33 : ∀ F ∈ fam0, ∃ W ∈ planes0, W.toFinset = F := fam0_planes0

private theorem planes1_fam1_34 : ∀ V ∈ planes1, V.toFinset ∈ fam1 := planes1_fam1

private theorem fam1_planes1_35 : ∀ F ∈ fam1, ∃ W ∈ planes1, W.toFinset = F := fam1_planes1

end CertificateChecks.Batch5071

namespace Certificates

open CertificateChecks.Batch5071 in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.HF in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5 in
theorem certificate5071 : (fam0.card = 4)
    ∧ (fam1.card = 4)
    ∧ ((1 : Perm (Fin 16)) ∈ n24L)
    ∧ (mulClosedChkP n24L = true)
    ∧ (invClosedChkP n24L = true)
    ∧ (n24L.Nodup)
    ∧ (n24L.length = 24)
    ∧ ((1 : Perm (Fin 16)) ∈ d8L)
    ∧ (mulClosedChkP d8L = true)
    ∧ (invClosedChkP d8L = true)
    ∧ (d8L.Nodup)
    ∧ (d8L.length = 8)
    ∧ (yHat ∈ n24L)
    ∧ (wHat ∈ n24L)
    ∧ (yHat ∈ d8L)
    ∧ (d8L.all (fun d => decide (d ∈ n24L)) = true)
    ∧ (v4L.all (fun v => decide (v ∈ d8L)) = true)
    ∧ (n24L.all (fun m => v4L.all fun v => decide (m * v * m⁻¹ ∈ v4L)) = true)
    ∧ (v4L.all (fun v => decide (cHat * v * cHat⁻¹ ∈ v4L)) = true)
    ∧ (cHat ∉ n24L)
    ∧ (n24L.all (fun A => linChk A && decide (Ppl.image A = Ppl)) = true)
    ∧ (IsLin16 twPerm)
    ∧ (Ppl.image twPerm = Ppl)
    ∧ (Qpl.image twPerm = Qpl)
    ∧ (fam0.image (fun V => V.image twPerm) = fam1)
    ∧ (fam1.image (fun V => V.image twPerm) = fam0)
    ∧ (twPerm * yHat * twPerm⁻¹ = yHat)
    ∧ (twPerm * wHat = wHat * twPerm)
    ∧ ((List.finRange 16).all (fun i => decide (actF gTw i = twPerm i)) = true)
    ∧ (allQ2 gN n24Entry = true)
    ∧ (∃ m : Perm (Fin 16), IsLin16 m ∧ Qpl.image m ≠ Qpl ∧ Qpl.image m ∩ Qpl = {0} ∧
      Qpl.image m ∩ Ppl = {0} ∧
      ∀ V ∈ fam0, V.image yHat ∈ fam0 ∧ V.image wHat ∈ fam0 ∧ V.image m ∈ fam0)
    ∧ (∃ m : Perm (Fin 16), IsLin16 m ∧ Qpl.image m ≠ Qpl ∧ Qpl.image m ∩ Qpl = {0} ∧
      Qpl.image m ∩ Ppl = {0} ∧
      ∀ V ∈ fam1, V.image yHat ∈ fam1 ∧ V.image wHat ∈ fam1 ∧ V.image m ∈ fam1)
    ∧ (∀ V ∈ planes0, V.toFinset ∈ fam0)
    ∧ (∀ F ∈ fam0, ∃ W ∈ planes0, W.toFinset = F)
    ∧ (∀ V ∈ planes1, V.toFinset ∈ fam1)
    ∧ (∀ F ∈ fam1, ∃ W ∈ planes1, W.toFinset = F)
    ∧ (Qpl ∈ fam0)
    ∧ (Qpl ∈ fam1)
    ∧ (G72L.length = 72)
    ∧ (G72L.Nodup)
    ∧ ((1 : Perm (Fin 16)) ∈ G72L)
    ∧ (mulClosedChkP G72L = true)
    ∧ (invClosedChkP G72L = true)
    ∧ (G72L.all (fun m => linChk m && fam0Chk m) = true)
    ∧ (allQ2 gFam (famEntry G72L) = true)
    ∧ (n24L.all (fun A => decide (A ∈ G72L)) = true)
    ∧ (cHat ∈ G72L)
    ∧ (n24L.getD 6 1 ∈ n24L)
    ∧ (yHat ≠ 1)
    ∧ (n24L.all (fun b => n24L.all fun c => d8Chk b c) = true) :=
  ⟨fam0_card_0, fam1_card_1, one_mem_n24L_2, n24L_mul_chk_3, n24L_inv_chk_4, n24L_nodup_5,
    n24L_length_6, one_mem_d8L_7, d8L_mul_chk_8, d8L_inv_chk_9, d8L_nodup_10, d8L_length_11,
    yHat_mem_n24L_12, wHat_mem_n24L_13, yHat_mem_d8L_14, d8L_sub_n24L_chk_15,
    v4L_sub_d8L_chk_16, v4L_normal_chk_17, cHat_v4L_chk_18, cHat_not_mem_n24L_19,
    n24L_lin_chk_20, twPerm_lin_21, twPerm_Ppl_22, twPerm_Qpl_23, twPerm_fam0_24,
    twPerm_fam1_25, twPerm_yHat_26, twPerm_wHat_27, actF_gTw_chk_28, n24_enum_29,
    n24_gen_hyps_fam0_30, n24_gen_hyps_fam1_31, planes0_fam0_32, fam0_planes0_33,
    planes1_fam1_34, fam1_planes1_35, Qpl_mem_fam0_36, Qpl_mem_fam1_37, G72L_length_38,
    G72L_nodup_39, one_mem_G72L_40, G72L_mul_chk_41, G72L_inv_chk_42, G72L_facts_43,
    fam_enum_44, n24_le_G72_chk_45, cHat_mem_G72L_46, n24g_mem_47, yHat_ne_one_48,
    d8_enum_49⟩

end Certificates
