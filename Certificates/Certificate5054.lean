module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.C3.Layer2.L5C0Base
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

namespace CertificateChecks.Batch5054

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

set_option maxRecDepth 100000

private theorem n24L_mul_chk_0 : mulClosedChkP n24L = true := by
  decide +kernel

private theorem n24L_inv_chk_1 : invClosedChkP n24L = true := by
  decide +kernel

private theorem one_mem_n24L_2 : (1 : Perm (Fin 16)) ∈ n24L := by
  decide +kernel

private theorem n24L_nodup_3 : n24L.Nodup := by
  decide +kernel

private theorem n24L_length_4 : n24L.length = 24 := by
  decide +kernel

private theorem yHat_mem_n24L_5 : yHat ∈ n24L := by
  decide +kernel

private theorem actF_T5_cases_chk_6 : allT5.all (fun t => decide ((∀ i : Fin 16, actF t i = i) ∨
    (∀ i : Fin 16, actF t i = yHat i))) = true := by
  decide +kernel

end CertificateChecks.Batch5054

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5054 : (mulClosedChkP n24L = true)
    ∧ (invClosedChkP n24L = true)
    ∧ ((1 : Perm (Fin 16)) ∈ n24L)
    ∧ (n24L.Nodup)
    ∧ (n24L.length = 24)
    ∧ (yHat ∈ n24L)
    ∧ (allT5.all (fun t => decide ((∀ i : Fin 16, actF t i = i) ∨
    (∀ i : Fin 16, actF t i = yHat i))) = true) := by
  exact ⟨CertificateChecks.Batch5054.n24L_mul_chk_0, CertificateChecks.Batch5054.n24L_inv_chk_1, CertificateChecks.Batch5054.one_mem_n24L_2, CertificateChecks.Batch5054.n24L_nodup_3, CertificateChecks.Batch5054.n24L_length_4, CertificateChecks.Batch5054.yHat_mem_n24L_5, CertificateChecks.Batch5054.actF_T5_cases_chk_6⟩

end Certificates
