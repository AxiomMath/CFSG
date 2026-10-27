module

public import CFSG.GH74.KGroups.A7Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import Certificates.Kernel.PermCent.KG5109

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A7 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.A7 in
open CFSG.Certificates CFSG.Sporadic.Schreier in
theorem certificate5109 : (QP.check = true ∧ QP.orderCertificate = 2520)
    ∧ (QA.check = true ∧ QA.orderCertificate = 5040)
    ∧ (orderIs pa 2 = true ∧ orderIs pb 5 = true ∧ pairInvB ws pa pb = true)
    ∧ (normCheck QP QA.original.toList pa pb = true)
    ∧ (centTrivCheck (elemsT QA) pa pb = true)
    ∧ (inner3check (elemsT QA) QP = true)
    ∧ (pairCountB QP 2 5 ws = 5040) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ K5109.kQP.1,
    (orderCertificate_eq_orderV _).trans K5109.kQP.2⟩,
    ⟨check_certificate_of _ _ _ _ _ K5109.kQA.1, (orderCertificate_eq_orderV _).trans K5109.kQA.2⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ev_cOf pa, ← ev_cOf pb, orderIs_C, orderIs_C, pairInvB_C]
    exact K5109.kOrd
  · rw [← map_cOf_ev QA.original.toList, ← ev_cOf pa, ← ev_cOf pb, norm_C]
    exact K5109.kNorm
  · rw [elemsT_eq_elemsC, ← ev_cOf pa, ← ev_cOf pb, centTriv_C]
    exact K5109.kCent
  · rw [elemsT_eq_elemsC, inner3_C]
    exact K5109.kInner3
  · rw [pairCount_C]
    exact K5109.kCount

end Certificates
