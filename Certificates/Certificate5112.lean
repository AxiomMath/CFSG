
module

public import Certificates.Certificate5112Base

public import CFSG.GH74.KGroups.CoverL34Inputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5112

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L34 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

theorem certificate5112 : (QE.check = true ∧ QE.orderCertificate = 16)
    ∧ (sqOneCheck (elemsT QE) = true)
    ∧ (conjWordsCheck [PA, PB] eg0 cws (elemsT QE) = true)
    ∧ (indepCheck eg0 eg1 eg2 = true)
    ∧ (leCheck QE QP = true)
    ∧ (QE.sift eg0 0 = true)
    ∧ (QE.sift eg1 0 = true)
    ∧ (QE.sift eg2 0 = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qe_5112K.1,
    (orderCertificate_eq_orderV _).trans qe_5112K.2⟩, ?_, ?_, indep_5112K, ?_, ?_, ?_, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact sq_5112K
  · rw [elemsT_eq_elemsV]
    exact conj_5112K
  · simp only [leCheck, sift_eq_siftP]
    exact le_5112K
  · rw [sift_eq_siftP]
    exact sift_5112K.1
  · rw [sift_eq_siftP]
    exact sift_5112K.2.1
  · rw [sift_eq_siftP]
    exact sift_5112K.2.2


end Certificates
