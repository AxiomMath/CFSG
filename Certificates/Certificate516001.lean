module

public import Certificates.Data.S5RowsU33
import CFSG.Certificates.Kernel.Census.CatFacts.LeCheck
import Certificates.Kernel.KGroupsE.K516001

public section

namespace Certificates

open CFSG.GH74.KGroups Certificates.S5Rows Certificates.S5RowsU33 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups Certificates.S5RowsU33 in
theorem certificate516001 : (QSA.check = true ∧ QSA.orderCertificate = 64 ∧ leCheck QSA U33.QA = true) ∧
    u33RowsF1a () = true ∧ u33RowsF1b () = true ∧ u33RowsF1c () = true := by
  have hp : inQP = fun x => siftP U33.QP x 0 := funext fun x => sift_eq_siftP _ _ _
  refine ⟨⟨check_certificate_of _ _ _ _ _ qs_516001K.1,
    (orderCertificate_eq_orderV _).trans qs_516001K.2, ?_⟩, ?_, ?_, ?_⟩
  · rw [leCheck_eq_siftP]
    exact le_516001K
  · change threeCycCheck (elemsT QSA) (elemsT U33.QP) inQP = true
    rw [elemsT_eq_elemsV QSA, elemsT_eq_elemsV U33.QP, hp]
    exact f1a_516001K
  · change conjMulCheck (elemsT QSA) (elemsT U33.QA) inQP = true
    rw [elemsT_eq_elemsV QSA, elemsT_eq_elemsV U33.QA, hp]
    exact f1b_516001K
  · change uniqueOuterCheck (elemsT QSA) inQP = true
    rw [elemsT_eq_elemsV QSA, hp]
    exact f1c_516001K

end Certificates
