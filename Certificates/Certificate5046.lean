module

public import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5046

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem T5_cent_R_le_chk_0 : allT5.all (fun t => imp (decide (t ∉ Rml))
    (decide ((Rml.filter (fun r => decide (r * t = t * r))).length ≤ 4))) = true := by
  decide +kernel

private theorem T5_cent_P_ne_chk_1 : allT5.all (fun t => imp (decide (t ∉ Rml))
    (Pml.any fun p => decide (p ≠ 1 ∧ p * t = t * p))) = true := by
  decide +kernel

private theorem wm_cycles_P_chk_2 : Pml.all (fun p => imp (decide (p ≠ 1)) (Pml.all fun p' =>
    imp (decide (p' ≠ 1)) (decide (p' = p ∨ p' = wm * p * wm⁻¹ ∨
      p' = wm * (wm * p * wm⁻¹) * wm⁻¹)))) = true := by
  decide +kernel

end CertificateChecks.Batch5046

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5046 : (allT5.all (fun t => imp (decide (t ∉ Rml))
    (decide ((Rml.filter (fun r => decide (r * t = t * r))).length ≤ 4))) = true)
    ∧ (allT5.all (fun t => imp (decide (t ∉ Rml))
    (Pml.any fun p => decide (p ≠ 1 ∧ p * t = t * p))) = true)
    ∧ (Pml.all (fun p => imp (decide (p ≠ 1)) (Pml.all fun p' =>
    imp (decide (p' ≠ 1)) (decide (p' = p ∨ p' = wm * p * wm⁻¹ ∨
      p' = wm * (wm * p * wm⁻¹) * wm⁻¹)))) = true) := by
  exact ⟨CertificateChecks.Batch5046.T5_cent_R_le_chk_0, CertificateChecks.Batch5046.T5_cent_P_ne_chk_1, CertificateChecks.Batch5046.wm_cycles_P_chk_2⟩

end Certificates
