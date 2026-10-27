module

public import CFSG.GH74.KGroups.A6Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import Certificates.Kernel.PermCent.KG5108
public import Certificates.Certificate43

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.A6 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix CFSG.Quasithin in
theorem certificate5108 : (QP.check = true ∧ QP.orderCertificate = 360)
    ∧ (QA.check = true ∧ QA.orderCertificate = 1440)
    ∧ (orderIs pa 2 = true ∧ orderIs pb 4 = true ∧ pairInvB ws pa pb = true)
    ∧ (normCheck QP QA.original.toList pa pb = true)
    ∧ (centTrivCheck (elemsT QA) pa pb = true)
    ∧ (e9free (elemsT QA) = true)
    ∧ (inner3check (elemsT QA) QP = true)
    ∧ (cent3check (elemsT QP) = true)
    ∧ (solvCheck (elemsT QA) (elemsT QP) = true)
    ∧ (pairCountB QP 2 4 ws = 1440) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ K5108.kQP.1,
    (orderCertificate_eq_orderV _).trans K5108.kQP.2⟩,
    ⟨check_certificate_of _ _ _ _ _ K5108.kQA.1, (orderCertificate_eq_orderV _).trans K5108.kQA.2⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ev_cOf pa, ← ev_cOf pb, orderIs_C, orderIs_C, pairInvB_C]
    exact K5108.kOrd
  · rw [← map_cOf_ev QA.original.toList, ← ev_cOf pa, ← ev_cOf pb, norm_C]
    exact K5108.kNorm
  · rw [elemsT_eq_elemsC, ← ev_cOf pa, ← ev_cOf pb, centTriv_C]
    exact K5108.kCent
  · rw [elemsT_eq_elemsC, e9free_C]
    exact K5108.kE9
  · rw [elemsT_eq_elemsC, inner3_C]
    exact K5108.kInner3
  · rw [elemsT_eq_elemsC, cent3_C]
    exact K5108.kCent3
  · rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
    refine solv_C _ _ _ K5108.kSolv fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact pf_le_two 2 3 3 0 Nat.prime_two Nat.prime_three
    · exact pf_le_two 2 5 1 1 Nat.prime_two Nat.prime_five
    · exact pf_le_two 2 3 3 1 Nat.prime_two Nat.prime_three
  · rw [pairCount_C]
    exact K5108.kCount

end Certificates
