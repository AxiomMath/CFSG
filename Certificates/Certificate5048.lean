module

public import CFSG.GH74.GLS.C3.Layer2.L5B5
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public import CFSG.GH74.GLS.C3.Layer2.L5B12Inputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B5
meta import CFSG.GH74.GLS.C3.Layer2.L5B12Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5048

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem mg1_cert_chk_0 : S0l.all (fun Y => S0l.all fun E =>
    imp (decide (Y * Y = 1) && decide (E * E = 1) && decide ((Y * E) ^ 4 = 1) &&
      decide ((Y * E) ^ 2 ≠ 1) && decide ((Y * E) ^ 2 ≠ vS0))
      (X0b Y || X0b (vS0 * Y) || X0b E || X0b (vS0 * E))) = true := by
  decide +kernel

private theorem exists_yE_chk_1 : allT5.all (fun t₀ =>
    imp (decide ((emb 5 t₀ * a0perm 5) * (emb 5 t₀ * a0perm 5) = 1))
      (allT5.any fun mY => Rml.any fun mE =>
        decide (mY * mY = 1) && decide (mY ∉ Rml) && mixb mE &&
        decide (emb 5 mY * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mY) &&
        decide (emb 5 mE * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mE) &&
        decide ((emb 5 mY * emb 5 mE) ^ 2 = vS0))) = true := by
  decide +kernel

private theorem S0_invol_nm_chk_2 : S0l.all (fun p => imp (decide (p * p = 1)) (imp (decide (p ≠ 1))
    (decide (numMoved p = 4 ∨ numMoved p = 8)))) = true := by
  decide +kernel

private theorem S0_invol_nT_nm8_chk_3 : S0l.all (fun p => imp (decide (p * p = 1)) (imp (decide (p ≠ 1))
    (imp (allT5.all fun m => decide (p ≠ emb 5 m)) (decide (numMoved p = 8))))) = true := by
  decide +kernel

end CertificateChecks.Batch5048

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5048 : (S0l.all (fun Y => S0l.all fun E =>
    imp (decide (Y * Y = 1) && decide (E * E = 1) && decide ((Y * E) ^ 4 = 1) &&
      decide ((Y * E) ^ 2 ≠ 1) && decide ((Y * E) ^ 2 ≠ vS0))
      (X0b Y || X0b (vS0 * Y) || X0b E || X0b (vS0 * E))) = true)
    ∧ (allT5.all (fun t₀ =>
    imp (decide ((emb 5 t₀ * a0perm 5) * (emb 5 t₀ * a0perm 5) = 1))
      (allT5.any fun mY => Rml.any fun mE =>
        decide (mY * mY = 1) && decide (mY ∉ Rml) && mixb mE &&
        decide (emb 5 mY * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mY) &&
        decide (emb 5 mE * (emb 5 t₀ * a0perm 5) = (emb 5 t₀ * a0perm 5) * emb 5 mE) &&
        decide ((emb 5 mY * emb 5 mE) ^ 2 = vS0))) = true)
    ∧ (S0l.all (fun p => imp (decide (p * p = 1)) (imp (decide (p ≠ 1))
    (decide (numMoved p = 4 ∨ numMoved p = 8)))) = true)
    ∧ (S0l.all (fun p => imp (decide (p * p = 1)) (imp (decide (p ≠ 1))
    (imp (allT5.all fun m => decide (p ≠ emb 5 m)) (decide (numMoved p = 8))))) = true) := by
  exact ⟨CertificateChecks.Batch5048.mg1_cert_chk_0, CertificateChecks.Batch5048.exists_yE_chk_1, CertificateChecks.Batch5048.S0_invol_nm_chk_2, CertificateChecks.Batch5048.S0_invol_nT_nm8_chk_3⟩

end Certificates
