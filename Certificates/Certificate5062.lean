module

public import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C4aInputs
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
meta import CFSG.GH74.GLS.C3.Layer2.L5C4aInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5062

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem d8L_length_0 : d8L.length = 8 := by
  decide +kernel

private theorem Dg_zero_1 : Dg 0 = 1 := by
  decide +kernel

private theorem Dg_one_2 : Dg 1 = yHat := by
  decide +kernel

private theorem Dg_mul_chk_3 : (List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    decide (Dg j * Dg k = Dg (mulIdx j k))) = true := by
  decide +kernel

private theorem Dg_inj_chk_4 : (List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    imp (decide (Dg j = Dg k)) (decide (j = k))) = true := by
  decide +kernel

private theorem Dg_lin_chk_5 : (List.finRange 8).all (fun j => (List.finRange 16).all fun a =>
    (List.finRange 16).all fun b =>
      decide (Dg j (xor16 a b) = xor16 (Dg j a) (Dg j b))) = true := by
  decide +kernel

private theorem Dg_mem_chk_6 : (List.finRange 8).all (fun k => decide (Dg k ∈ d8L)) = true := by
  decide +kernel

private theorem Dg_exists_chk_7 : d8L.all (fun d => (List.finRange 8).any fun k => decide (d = Dg k)) =
    true := by
  decide +kernel

private theorem mulIdx_zero_left_chk_8 : (List.finRange 8).all (fun k => decide (mulIdx 0 k = k)) = true := by
  decide +kernel

private theorem mulIdx_zero_right_chk_9 : (List.finRange 8).all (fun k => decide (mulIdx k 0 = k)) = true := by
  decide +kernel

private theorem mulIdx_one_one_10 : mulIdx 1 1 = 0 := by
  decide +kernel

private theorem mulIdx_zero_zero_11 : mulIdx 0 0 = 0 := by
  decide +kernel

private theorem Dg_tr16_chk_12 : (List.finRange 8).all (fun j => (List.finRange 16).all fun w =>
    decide (Dg j * tr16 w = tr16 (Dg j w) * Dg j)) = true := by
  decide +kernel

end CertificateChecks.Batch5062

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5062 : (d8L.length = 8)
    ∧ (Dg 0 = 1)
    ∧ (Dg 1 = yHat)
    ∧ ((List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    decide (Dg j * Dg k = Dg (mulIdx j k))) = true)
    ∧ ((List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    imp (decide (Dg j = Dg k)) (decide (j = k))) = true)
    ∧ ((List.finRange 8).all (fun j => (List.finRange 16).all fun a =>
    (List.finRange 16).all fun b =>
      decide (Dg j (xor16 a b) = xor16 (Dg j a) (Dg j b))) = true)
    ∧ ((List.finRange 8).all (fun k => decide (Dg k ∈ d8L)) = true)
    ∧ (d8L.all (fun d => (List.finRange 8).any fun k => decide (d = Dg k)) =
    true)
    ∧ ((List.finRange 8).all (fun k => decide (mulIdx 0 k = k)) = true)
    ∧ ((List.finRange 8).all (fun k => decide (mulIdx k 0 = k)) = true)
    ∧ (mulIdx 1 1 = 0)
    ∧ (mulIdx 0 0 = 0)
    ∧ ((List.finRange 8).all (fun j => (List.finRange 16).all fun w =>
    decide (Dg j * tr16 w = tr16 (Dg j w) * Dg j)) = true) := by
  exact ⟨CertificateChecks.Batch5062.d8L_length_0, CertificateChecks.Batch5062.Dg_zero_1, CertificateChecks.Batch5062.Dg_one_2, CertificateChecks.Batch5062.Dg_mul_chk_3, CertificateChecks.Batch5062.Dg_inj_chk_4, CertificateChecks.Batch5062.Dg_lin_chk_5, CertificateChecks.Batch5062.Dg_mem_chk_6, CertificateChecks.Batch5062.Dg_exists_chk_7, CertificateChecks.Batch5062.mulIdx_zero_left_chk_8, CertificateChecks.Batch5062.mulIdx_zero_right_chk_9, CertificateChecks.Batch5062.mulIdx_one_one_10, CertificateChecks.Batch5062.mulIdx_zero_zero_11, CertificateChecks.Batch5062.Dg_tr16_chk_12⟩

end Certificates
