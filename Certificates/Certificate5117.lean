module

public import CFSG.GH74.KGroups.L27Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import Certificates.Kernel.PermCent.KG5117
public import Certificates.Certificate43

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L27 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L27 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix in
theorem certificate5117 : (QP.check = true ∧ QP.orderCertificate = 168)
    ∧ (QA.check = true ∧ QA.orderCertificate = 336)
    ∧ (orderIs pa 2 = true ∧ orderIs pb 3 = true ∧ pairInvB ws pa pb = true)
    ∧ (normCheck QP QA.original.toList pa pb = true)
    ∧ (centTrivCheck (elemsT QA) pa pb = true)
    ∧ (inner3check (elemsT QA) QP = true)
    ∧ (solvCheck (elemsT QA) (elemsT QP) = true)
    ∧ (pairCountB QP 2 3 ws = 336) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ K5117.kQP.1,
    (orderCertificate_eq_orderV _).trans K5117.kQP.2⟩,
    ⟨check_certificate_of _ _ _ _ _ K5117.kQA.1, (orderCertificate_eq_orderV _).trans K5117.kQA.2⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ev_cOf pa, ← ev_cOf pb, orderIs_C, orderIs_C, pairInvB_C]
    exact K5117.kOrd
  · rw [← map_cOf_ev QA.original.toList, ← ev_cOf pa, ← ev_cOf pb, norm_C]
    exact K5117.kNorm
  · rw [elemsT_eq_elemsC, ← ev_cOf pa, ← ev_cOf pb, centTriv_C]
    exact K5117.kCent
  · rw [elemsT_eq_elemsC, inner3_C]
    exact K5117.kInner3
  · rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
    refine solv_C _ _ _ K5117.kSolv fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact pf_le_two 2 3 1 1 Nat.prime_two Nat.prime_three
    · exact pf_le_two 2 3 3 0 Nat.prime_two Nat.prime_three
  · rw [pairCount_C]
    exact K5117.kCount

end Certificates
