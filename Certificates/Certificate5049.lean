module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public import CFSG.GH74.GLS.C3.Layer2.L5B2Inputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B2Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5049

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem Wl_cover_chk_0 : allT5.all (fun t => Wl.any fun w => decide (evalW gT w = t)) = true := by
  decide +kernel

private theorem Rels_chk_1 : Rels.all (fun r => decide (evalW gT r = 1)) = true := by
  decide +kernel

private theorem gT_mem_chk_2 : T5b (gT 0) = true ∧ T5b (gT 1) = true ∧ T5b (gT 2) = true := by
  decide +kernel

private theorem main27_true_3 : main27 = true := by
  decide +kernel

private theorem nm_id_chk_4 : allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (decide (nmE t = 8 ↔ (t ∈ Rml ∧ t ∉ Pml ∧ t ∉ Qml))))) = true := by
  decide +kernel

private theorem a0_conj_PQ_chk_5 : Pml.all (fun p => Qml.any fun q =>
    decide (a0perm 5 * emb 5 p * (a0perm 5)⁻¹ = emb 5 q)) = true := by
  decide +kernel

private theorem a0_conj_QP_chk_6 : Qml.all (fun q => Pml.any fun p =>
    decide (a0perm 5 * emb 5 q * (a0perm 5)⁻¹ = emb 5 p)) = true := by
  decide +kernel

end CertificateChecks.Batch5049

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5049 : (allT5.all (fun t => Wl.any fun w => decide (evalW gT w = t)) = true)
    ∧ (Rels.all (fun r => decide (evalW gT r = 1)) = true)
    ∧ (T5b (gT 0) = true ∧ T5b (gT 1) = true ∧ T5b (gT 2) = true)
    ∧ (main27 = true)
    ∧ (allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (decide (nmE t = 8 ↔ (t ∈ Rml ∧ t ∉ Pml ∧ t ∉ Qml))))) = true)
    ∧ (Pml.all (fun p => Qml.any fun q =>
    decide (a0perm 5 * emb 5 p * (a0perm 5)⁻¹ = emb 5 q)) = true)
    ∧ (Qml.all (fun q => Pml.any fun p =>
    decide (a0perm 5 * emb 5 q * (a0perm 5)⁻¹ = emb 5 p)) = true) := by
  exact ⟨CertificateChecks.Batch5049.Wl_cover_chk_0, CertificateChecks.Batch5049.Rels_chk_1, CertificateChecks.Batch5049.gT_mem_chk_2, CertificateChecks.Batch5049.main27_true_3, CertificateChecks.Batch5049.nm_id_chk_4, CertificateChecks.Batch5049.a0_conj_PQ_chk_5, CertificateChecks.Batch5049.a0_conj_QP_chk_6⟩

end Certificates
