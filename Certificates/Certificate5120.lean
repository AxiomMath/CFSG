module

public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import Certificates.Kernel.PermCent.KG5120A
import Certificates.Kernel.PermCent.KG5120B
import Certificates.Kernel.PermCent.KG5120C
import Certificates.Kernel.PermCent.KG5120D

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum

namespace Certificates

private theorem e27_5120 : e27free (elemsT QA) = true := by
  rw [elemsT_eq_elemsC, e27free_C, e27freeF_eq]
  have hb : ∀ j < 8, L33A.e27B j = true := by
    intro j hj
    interval_cases j
    exacts [L33A.e27B0, L33A.e27B1, L33A.e27B2, L33A.e27B3, L33A.e27B4, L33A.e27B5, L33A.e27B6,
      L33A.e27B7]
  exact all_of_chunks _ _ 1404 8 L33A.kLen hb

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L33 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix in
theorem certificate5120 : (QP13.check = true ∧ QP13.orderCertificate = 5616)
    ∧ (QP.check = true ∧ QP.orderCertificate = 5616)
    ∧ (QA.check = true ∧ QA.orderCertificate = 11232)
    ∧ (orderIs PA 2 = true ∧ orderIs PB 3 = true ∧ pairInvB ws PA PB = true)
    ∧ (normCheck QP QA.original.toList PA PB = true)
    ∧ (centTrivCheck (elemsT QA) PA PB = true)
    ∧ (e9free (elemsT QA) = true)
    ∧ (e27free (elemsT QA) = true)
    ∧ (inner3check (elemsT QA) QP = true)
    ∧ (cent3check (elemsT QP) = true)
    ∧ (solvCheck (elemsT QA) (elemsT QP) = true)
    ∧ (blockHom 13 13 (pa, pa') = PA ∧ blockHom 13 13 (pb, pb') = PB)
    ∧ (pairCountB QP 2 3 ws = 11232) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ K5120.kQP13.1,
    (orderCertificate_eq_orderV _).trans K5120.kQP13.2⟩,
    ⟨check_certificate_of _ _ _ _ _ K5120.kQP.1, (orderCertificate_eq_orderV _).trans K5120.kQP.2⟩,
    ⟨check_certificate_of _ _ _ _ _ K5120.kQA.1, (orderCertificate_eq_orderV _).trans K5120.kQA.2⟩,
    ?_, ?_, ?_, ?_, e27_5120, ?_, ?_, ?_, K5120.kBlk, ?_⟩
  · rw [← ev_cOf PA, ← ev_cOf PB, orderIs_C, orderIs_C, pairInvB_C]
    exact K5120.kOrd
  · rw [← map_cOf_ev QA.original.toList, ← ev_cOf PA, ← ev_cOf PB, norm_C]
    exact K5120.kNorm
  · rw [elemsT_eq_elemsC, ← ev_cOf PA, ← ev_cOf PB, centTriv_C]
    exact K5120.kCent
  · rw [elemsT_eq_elemsC, e9free_C]
    exact K5120.kE9
  · rw [elemsT_eq_elemsC, inner3_C]
    exact K5120.kInner3
  · rw [elemsT_eq_elemsC, cent3_C]
    exact K5120.kCent3
  · rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
    refine solv_C _ _ _ K5120.kSolv fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact pf_le_two 2 3 4 1 Nat.prime_two Nat.prime_three
    · exact pf_le_two 2 3 3 1 Nat.prime_two Nat.prime_three
  · rw [pairCount_C]
    exact K5120.kCount

end Certificates
