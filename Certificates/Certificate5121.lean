module

public import CFSG.GH74.KGroups.L33TablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5121

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L33 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5121 : (QS.check = true ∧ QS.orderCertificate = 16)
    ∧ (invConjCheck (elemsT QP) t0 = true)
    ∧ (smallCheck (elemsT QS) s0 = true)
    ∧ (sR ^ 8 = 1 ∧ sT ^ 2 = 1 ∧ sT * sR * sT⁻¹ = sR ^ 3 ∧
    (∀ i : Fin 8, ∀ e : Fin 2, sR ^ (i : ℕ) * sT ^ (e : ℕ) = 1 → i = 0 ∧ e = 0))
    ∧ (leCheck QS QP = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qs_5121K.1,
    (orderCertificate_eq_orderV _).trans qs_5121K.2⟩, ?_, ?_, rel_5121K, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact inv_5121K
  · rw [elemsT_eq_elemsV]
    exact small_5121K
  · simp only [leCheck, sift_eq_siftP]
    exact le_5121K

end Certificates
