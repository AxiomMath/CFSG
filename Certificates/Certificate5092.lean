module

public import CFSG.GH74.GLS.C3.Prop121.ModelFive
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsGeneric
public import Mathlib.GroupTheory.Sylow
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveSInputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveSInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.Model.Facts

namespace CertificateChecks.Batch5092

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.Model.Facts

set_option maxRecDepth 100000

private theorem a0_sq_0 : a0perm 5 * a0perm 5 = 1 := by
  decide +kernel

private theorem sign_a0_1 : sign (a0perm 5) = 1 := by
  decide +kernel

private theorem a0_norm_T5_2 : ∀ t ∈ allT5, ∃ t' ∈ allT5, a0perm 5 * emb 5 t * (a0perm 5)⁻¹ = emb 5 t' := by
  decide +kernel

private theorem a0_notin_T5_3 : ∀ t ∈ allT5, emb 5 t ≠ a0perm 5 := by
  decide +kernel

private theorem a0_f1_4 : a0perm 5 * emb 5 f1 * (a0perm 5)⁻¹ = emb 5 e1 := by
  decide +kernel

private theorem S0l_facts_5 : S0l.length = 64 ∧ S0l.Nodup := by
  decide +kernel

private theorem class_check_6 : classAll S0l = true := by
  decide +kernel

private theorem cent_check_7 : centAll S0l allT5 = true := by
  decide +kernel

end CertificateChecks.Batch5092

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.Model.Facts in
theorem certificate5092 : (a0perm 5 * a0perm 5 = 1)
    ∧ (sign (a0perm 5) = 1)
    ∧ (∀ t ∈ allT5, ∃ t' ∈ allT5, a0perm 5 * emb 5 t * (a0perm 5)⁻¹ = emb 5 t')
    ∧ (∀ t ∈ allT5, emb 5 t ≠ a0perm 5)
    ∧ (a0perm 5 * emb 5 f1 * (a0perm 5)⁻¹ = emb 5 e1)
    ∧ (S0l.length = 64 ∧ S0l.Nodup)
    ∧ (classAll S0l = true)
    ∧ (centAll S0l allT5 = true) := by
  exact ⟨CertificateChecks.Batch5092.a0_sq_0, CertificateChecks.Batch5092.sign_a0_1, CertificateChecks.Batch5092.a0_norm_T5_2, CertificateChecks.Batch5092.a0_notin_T5_3, CertificateChecks.Batch5092.a0_f1_4, CertificateChecks.Batch5092.S0l_facts_5, CertificateChecks.Batch5092.class_check_6, CertificateChecks.Batch5092.cent_check_7⟩

end Certificates
