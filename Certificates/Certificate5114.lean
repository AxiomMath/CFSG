module

public import CFSG.GH74.KGroups.CoverM23Inputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5114

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M23 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.M23 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5114 : (QP.check = true ∧ QP.orderCertificate = 10200960)
    ∧ (QE.check = true ∧ QE.orderCertificate = 16)
    ∧ (sqOneCheck (elemsT QE) = true)
    ∧ (conjWordsCheck [m23PermA, m23PermB] eg0 cws (elemsT QE) = true)
    ∧ (indepCheck eg0 eg1 eg2 = true)
    ∧ (leCheck QE QP = true)
    ∧ (QE.sift eg0 0 = true)
    ∧ (QE.sift eg1 0 = true)
    ∧ (QE.sift eg2 0 = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qp_5114K.1,
      (orderCertificate_eq_orderV _).trans qp_5114K.2⟩,
    ⟨check_certificate_of _ _ _ _ _ qe_5114K.1, (orderCertificate_eq_orderV _).trans qe_5114K.2⟩,
    ?_, ?_, indep_5114K, ?_, ?_, ?_, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact sq_5114K
  · rw [elemsT_eq_elemsV]
    exact conj_5114K
  · simp only [leCheck, sift_eq_siftP]
    exact le_5114K
  · rw [sift_eq_siftP]
    exact sift_5114K.1
  · rw [sift_eq_siftP]
    exact sift_5114K.2.1
  · rw [sift_eq_siftP]
    exact sift_5114K.2.2

end Certificates
