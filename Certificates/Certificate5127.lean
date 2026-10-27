module

public import CFSG.GH74.KGroups.M22Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.KGroups
open CFSG.GH74.KGroups.M22
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

namespace CertificateChecks.Batch5127

open CFSG
open CFSG.GH74
open CFSG.GH74.KGroups
open CFSG.GH74.KGroups.M22
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

set_option maxHeartbeats 0 in
private theorem QP_valid_0 : QP.check = true ∧ QP.orderCertificate = 443520 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem QE_valid_1 : QE.check = true ∧ QE.orderCertificate = 16 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem QE_sq_2 : sqOneCheck (elemsT QE) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem conj_ok_3 : conjWordsCheck [m22gA, m22gB] eg0 cws (elemsT QE) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem indep_ok_4 : indepCheck eg0 eg1 eg2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem QE_le_check_5 : leCheck QE QP = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem mem0_check_6 : QE.sift eg0 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem mem1_check_7 : QE.sift eg1 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem mem2_check_8 : QE.sift eg2 0 = true := by
  decide +kernel

end CertificateChecks.Batch5127

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.M22 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate5127 : (QP.check = true ∧ QP.orderCertificate = 443520)
    ∧ (QE.check = true ∧ QE.orderCertificate = 16)
    ∧ (sqOneCheck (elemsT QE) = true)
    ∧ (conjWordsCheck [m22gA, m22gB] eg0 cws (elemsT QE) = true)
    ∧ (indepCheck eg0 eg1 eg2 = true)
    ∧ (leCheck QE QP = true)
    ∧ (QE.sift eg0 0 = true)
    ∧ (QE.sift eg1 0 = true)
    ∧ (QE.sift eg2 0 = true) := by
  exact ⟨CertificateChecks.Batch5127.QP_valid_0, CertificateChecks.Batch5127.QE_valid_1, CertificateChecks.Batch5127.QE_sq_2, CertificateChecks.Batch5127.conj_ok_3, CertificateChecks.Batch5127.indep_ok_4, CertificateChecks.Batch5127.QE_le_check_5, CertificateChecks.Batch5127.mem0_check_6, CertificateChecks.Batch5127.mem1_check_7, CertificateChecks.Batch5127.mem2_check_8⟩

end Certificates
