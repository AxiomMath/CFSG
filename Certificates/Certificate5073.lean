module

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5ModelInputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5ModelInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5073

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem mk4_mem_Rlist5_0 : ∀ a b c d : Bool, mk4 e1 e2 f1 f2 a b c d ∈ Rlist5 := by
  decide +kernel

private theorem Rlist5_mk4_chk_1 : Rlist5.all (fun r => decide (∃ a b c d : Bool,
    r = mk4 e1 e2 f1 f2 a b c d)) = true := by
  decide +kernel

private theorem R_check_chk_2 : [e2, e1 * e2].all (fun β => [f2, f1 * f2].all fun γ =>
    decide (∀ a b c d : Bool, nmE (mk4 e1 β f1 γ a b c d) = nmE (mk4 e1 e2 f1 f2 a b c d) ∧
      mk4 e1 β f1 γ a b c d ∈ Rlist5)) = true := by
  decide +kernel

private theorem R_surj_chk_3 : [e2, e1 * e2].all (fun β => [f2, f1 * f2].all fun γ => Rlist5.all fun q =>
    decide (∃ a b c d : Bool, q = mk4 e1 β f1 γ a b c d)) = true := by
  decide +kernel

private theorem nm_outside_R_chk_4 : allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (imp (decide (t ∉ Rlist5)) (decide (nmE t = 4))))) = true := by
  decide +kernel

end CertificateChecks.Batch5073

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5073 : (∀ a b c d : Bool, mk4 e1 e2 f1 f2 a b c d ∈ Rlist5)
    ∧ (Rlist5.all (fun r => decide (∃ a b c d : Bool,
    r = mk4 e1 e2 f1 f2 a b c d)) = true)
    ∧ ([e2, e1 * e2].all (fun β => [f2, f1 * f2].all fun γ =>
    decide (∀ a b c d : Bool, nmE (mk4 e1 β f1 γ a b c d) = nmE (mk4 e1 e2 f1 f2 a b c d) ∧
      mk4 e1 β f1 γ a b c d ∈ Rlist5)) = true)
    ∧ ([e2, e1 * e2].all (fun β => [f2, f1 * f2].all fun γ => Rlist5.all fun q =>
    decide (∃ a b c d : Bool, q = mk4 e1 β f1 γ a b c d)) = true)
    ∧ (allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (imp (decide (t ∉ Rlist5)) (decide (nmE t = 4))))) = true) := by
  exact ⟨CertificateChecks.Batch5073.mk4_mem_Rlist5_0, CertificateChecks.Batch5073.Rlist5_mk4_chk_1, CertificateChecks.Batch5073.R_check_chk_2, CertificateChecks.Batch5073.R_surj_chk_3, CertificateChecks.Batch5073.nm_outside_R_chk_4⟩

end Certificates
