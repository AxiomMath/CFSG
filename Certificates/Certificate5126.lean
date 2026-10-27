module

public import CFSG.GH74.KGroups.M11TablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.LeCheck
import Certificates.Kernel.KGroupsE.K5126

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.M11 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5126 : (QS.check = true ∧ QS.orderCertificate = 16)
    ∧ (invConjCheck (elemsT Q) t0 = true)
    ∧ (smallCheck (elemsT QS) s0 = true)
    ∧ (sR ^ 8 = 1 ∧ sT ^ 2 = 1 ∧ sT * sR * sT⁻¹ = sR ^ 3 ∧
    (∀ i : Fin 8, ∀ e : Fin 2, sR ^ (i : ℕ) * sT ^ (e : ℕ) = 1 → i = 0 ∧ e = 0))
    ∧ (leCheck QS Q = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qs_5126K.1,
    (orderCertificate_eq_orderV _).trans qs_5126K.2⟩, ?_, ?_, rel_5126K, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact inv_5126K
  · rw [elemsT_eq_elemsV]
    exact small_5126K
  · rw [leCheck_eq_siftP]
    exact le_5126K

end Certificates
