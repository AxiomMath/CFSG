module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEnumInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model
open Equiv Perm Subgroup

namespace CertificateChecks.Batch5039

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model
open Equiv Perm Subgroup

private theorem Dl_spec_0 : ∀ d : Perm (Fin 4), d * x4 = x4 * d ↔ d ∈ Dl := by
  decide +kernel

private theorem plClosedB6_1 : plClosedB 6 = true := by
  decide +kernel

private theorem plClosedB7_2 : plClosedB 7 = true := by
  decide +kernel

private theorem tlFactsB6_3 : tlFactsB 6 = true := by
  decide +kernel

private theorem tlFactsB7_4 : tlFactsB 7 = true := by
  decide +kernel

end CertificateChecks.Batch5039

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.Model in
open Equiv Perm Subgroup in
theorem certificate5039 : (∀ d : Perm (Fin 4), d * x4 = x4 * d ↔ d ∈ Dl)
    ∧ (plClosedB 6 = true)
    ∧ (plClosedB 7 = true)
    ∧ (tlFactsB 6 = true)
    ∧ (tlFactsB 7 = true) := by
  exact ⟨CertificateChecks.Batch5039.Dl_spec_0, CertificateChecks.Batch5039.plClosedB6_1, CertificateChecks.Batch5039.plClosedB7_2, CertificateChecks.Batch5039.tlFactsB6_3, CertificateChecks.Batch5039.tlFactsB7_4⟩

end Certificates
