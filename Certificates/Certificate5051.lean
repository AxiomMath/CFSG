
module

public import Certificates.Certificate5051Base
import all Certificates.Certificate5051Base

public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
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
meta import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
import CFSG.Certificates.Kernel.L5.Fast
import CFSG.Certificates.Kernel.L5.Sh0TSound
import CFSG.Certificates.Kernel.L5.HFCIdx
import Certificates.Kernel.L5.Sh0Checks

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.Certificates.Kernel
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5051

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.Certificates.Kernel
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

end CertificateChecks.Batch5051

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5051 : ((List.finRange 16).all (fun i => decide (el16 i ∈ Rml)) = true)
    ∧ ((List.finRange 16).all (fun i => decide (idx16 (el16 i) = i)) = true)
    ∧ (Rml.all (fun r => decide (el16 (idx16 r) = r)) = true)
    ∧ ((List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    decide (el16 (xor16 i j) = el16 i * el16 j)) = true)
    ∧ (yy5 * yy5 = 1)
    ∧ (allT5.all (fun t => decide (t ∈ Rml ∨ t * yy5 ∈ Rml)) = true)
    ∧ ((List.finRange 16).all (fun i => decide (actF yy5 i = yHat i)) = true)
    ∧ ((List.finRange 16).all (fun i => decide (actF wm i = wHat i)) = true)
    ∧ (Sh0L.Nodup)
    ∧ (Sh0L.length = 128)
    ∧ (Sh1L.Nodup)
    ∧ (Sh1L.length = 128)
    ∧ (mulClosedChkP Sh0L = true)
    ∧ (invClosedChkP Sh0L = true)
    ∧ (mulClosedChkP Sh1L = true)
    ∧ (invClosedChkP Sh1L = true)
    ∧ ((1 : Perm (Fin 16)) ∈ Sh0L)
    ∧ (allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr16 yHat (s * t) = emb48 tr16 yHat s * emb48 tr16 yHat t)) = true)
    ∧ (allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr1 yHat1 (s * t) = emb48 tr1 yHat1 s * emb48 tr1 yHat1 t)) = true)
    ∧ (allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr16 yHat s = emb48 tr16 yHat t)) (decide (s = t))) = true)
    ∧ (allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr1 yHat1 s = emb48 tr1 yHat1 t)) (decide (s = t))) = true)
    ∧ (allT5.all (fun t => decide (emb48 tr16 yHat t ∈ Sh0L)) = true)
    ∧ (allT5.all (fun t => decide (emb48 tr1 yHat1 t ∈ Sh1L)) = true)
    ∧ (S0L0.length = 64)
    ∧ (S0L1.length = 64)
    ∧ (R1L.all (fun s => decide (s ∈ S0L0)) = true)
    ∧ (R1L.length = 16)
    ∧ (RhatL0.all (fun s => decide (s ∈ S0L0)) = true)
    ∧ (RhatL1.all (fun s => decide (s ∈ S0L1)) = true)
    ∧ (emb48 tr16 yHat 1 = 1)
    ∧ (emb48 tr1 yHat1 1 = 1)
    ∧ ((1 : Perm (Fin 16)) ∈ RhatL0)
    ∧ ((1 : Perm (Fin 16)) ∈ RhatL1)
    ∧ ((1 : Perm (Fin 16)) ∈ R1L)
    ∧ ((1 : Perm (Fin 16)) ∈ S0L0)
    ∧ ((1 : Perm (Fin 16)) ∈ S0L1)
    ∧ (mulClosedChkP RhatL0 = true)
    ∧ (invClosedChkP RhatL0 = true)
    ∧ (mulClosedChkP RhatL1 = true)
    ∧ (invClosedChkP RhatL1 = true)
    ∧ (mulClosedChkP R1L = true)
    ∧ (invClosedChkP R1L = true)
    ∧ (mulClosedChkP S0L0 = true)
    ∧ (invClosedChkP S0L0 = true)
    ∧ (mulClosedChkP S0L1 = true)
    ∧ (invClosedChkP S0L1 = true)
    ∧ (RhatL0.all (fun p => decide (p ∈ Sh0L)) = true)
    ∧ (RhatL1.all (fun p => decide (p ∈ Sh1L)) = true)
    ∧ (S0L0.all (fun p => decide (p ∈ Sh0L)) = true)
    ∧ (S0L1.all (fun p => decide (p ∈ Sh1L)) = true)
    ∧ (R1L.all (fun p => decide (p ∈ Sh0L)) = true)
    ∧ (yy5 ∈ Rml → False)
    ∧ (T5b yy5 = true)
    ∧ (T5b f1 = true) := by
  exact ⟨CertificateChecks.Batch5051.el16_mem_chk_0, CertificateChecks.Batch5051.idx16_el16_chk_1, CertificateChecks.Batch5051.el16_idx16_chk_2, CertificateChecks.Batch5051.el16_xor_chk_3, CertificateChecks.Batch5051.yy5_sq_4, CertificateChecks.Batch5051.T5_cases_chk_5, CertificateChecks.Batch5051.actF_yy5_chk_6, CertificateChecks.Batch5051.actF_wm_chk_7, CertificateChecks.Batch5051.Sh0L_nodup_8, CertificateChecks.Batch5051.Sh0L_length_9, CertificateChecks.Batch5051.Sh1L_nodup_10, CertificateChecks.Batch5051.Sh1L_length_11, CertificateChecks.Batch5051.Sh0L_mul_chk_12, CertificateChecks.Batch5051.Sh0L_inv_chk_13, CertificateChecks.Batch5051.Sh1L_mul_chk_14, CertificateChecks.Batch5051.Sh1L_inv_chk_15, CertificateChecks.Batch5051.one_mem_Sh0L_16, CertificateChecks.Batch5051.emb48_mul0_chk_17, CertificateChecks.Batch5051.emb48_mul1_chk_18, CertificateChecks.Batch5051.emb48_inj0_chk_19, CertificateChecks.Batch5051.emb48_inj1_chk_20, CertificateChecks.Batch5051.emb48_mem0_chk_21, CertificateChecks.Batch5051.emb48_mem1_chk_22, CertificateChecks.Batch5051.S0L0_length_23, CertificateChecks.Batch5051.S0L1_length_24, CertificateChecks.Batch5051.R1L_sub_S0L0_25, CertificateChecks.Batch5051.R1L_length_26, CertificateChecks.Batch5051.RhatL0_sub_27, CertificateChecks.Batch5051.RhatL1_sub_28, CertificateChecks.Batch5051.emb48_one0_29, CertificateChecks.Batch5051.emb48_one1_30, CertificateChecks.Batch5051.one_mem_RhatL0_31, CertificateChecks.Batch5051.one_mem_RhatL1_32, CertificateChecks.Batch5051.one_mem_R1L_33, CertificateChecks.Batch5051.one_mem_S0L0_34, CertificateChecks.Batch5051.one_mem_S0L1_35, CertificateChecks.Batch5051.RhatL0_mul_chk_36, CertificateChecks.Batch5051.RhatL0_inv_chk_37, CertificateChecks.Batch5051.RhatL1_mul_chk_38, CertificateChecks.Batch5051.RhatL1_inv_chk_39, CertificateChecks.Batch5051.R1L_mul_chk_40, CertificateChecks.Batch5051.R1L_inv_chk_41, CertificateChecks.Batch5051.S0L0_mul_chk_42, CertificateChecks.Batch5051.S0L0_inv_chk_43, CertificateChecks.Batch5051.S0L1_mul_chk_44, CertificateChecks.Batch5051.S0L1_inv_chk_45, CertificateChecks.Batch5051.RsubP0_le_Sh0_chk_46, CertificateChecks.Batch5051.RsubP1_le_Sh1_chk_47, CertificateChecks.Batch5051.S0subP0_le_Sh0_chk_48, CertificateChecks.Batch5051.S0subP1_le_Sh1_chk_49, CertificateChecks.Batch5051.R1subP_le_Sh0_chk_50, CertificateChecks.Batch5051.yy5_not_mem_check_51, CertificateChecks.Batch5051.yy5_mem_check_52, CertificateChecks.Batch5051.f1_mem_T5_check_53⟩

end Certificates
