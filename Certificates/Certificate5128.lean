module

public import CFSG.GH74.KGroups.Sz8Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpConjSound
import Certificates.Kernel.PermCent.KG5128A
import Certificates.Kernel.PermCent.KG5128B
import Certificates.Kernel.PermCent.KG5128D
import Certificates.Kernel.PermCent.KG5128F

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum CFSG.Certificates
  CFSG.Sporadic.Schreier

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.Sz8 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Quasithin CFSG.LieType.Ree CFSG.Blueprint Matrix in
open scoped LinearAlgebra.Projectivization in
theorem certificate5128 : (QP.check = true ∧ QP.orderCertificate = 29120)
    ∧ (QA.check = true ∧ QA.orderCertificate = 87360)
    ∧ (orderIs pa 2 = true ∧ orderIs pb 4 = true ∧ pairInvB ws pa pb = true)
    ∧ (normCheck QP QA.original.toList pa pb = true)
    ∧ (centTrivCheck (elemsT QA) pa pb = true)
    ∧ (solvCheck (elemsT QA) (elemsT QP) = true)
    ∧ (NativeChecks.pairCountE QP 2 4 ws = 87360) := by
  have hQP : ValidSchreier QP := check_certificate_of _ _ _ _ _ K5128.kQP.1
  have hQA : ValidSchreier QA := check_certificate_of _ _ _ _ _ K5128.kQA.1
  refine ⟨⟨hQP, (orderCertificate_eq_orderV _).trans K5128.kQP.2⟩,
    ⟨hQA, (orderCertificate_eq_orderV _).trans K5128.kQA.2⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ev_cOf pa, ← ev_cOf pb, orderIs_C, orderIs_C, pairInvB_C]
    exact K5128.kOrd
  · rw [← map_cOf_ev QA.original.toList, ← ev_cOf pa, ← ev_cOf pb, norm_C]
    exact K5128.kNorm
  · rw [elemsT_eq_elemsC, ← ev_cOf pa, ← ev_cOf pb, centTriv_C]
    exact K5128.kCent
  · rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
    have hle : QP.originalSubgroup ≤ QA.originalSubgroup := by
      rw [QP, QA, certificate_originalSubgroup, certificate_originalSubgroup, Subgroup.closure_le]
      intro g hg
      apply Subgroup.subset_closure
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
      rcases hg with rfl | rfl <;> simp
    have hgen : QP.original.toList = [ev (cOf pa), ev (cOf pb)] := by
      rw [ev_cOf, ev_cOf, QP, certificate_original]
    have hN := le_normalizer_of_normC QP QA hQP (cOf pa) (cOf pb) hgen K5128.kNorm
    have hc : Nat.card QA.originalSubgroup = 3 * Nat.card QP.originalSubgroup := by
      rw [card_group QA hQA, card_group QP hQP, orderCertificate_eq_orderV,
        orderCertificate_eq_orderV, K5128.kQA.2, K5128.kQP.2]
    have hs : solvC (elemsC QA) (elemsC QP) [64] = true :=
      solvC_of_conj QP QA hQP hQA hle hN hc (cOf pa) 64 K5128.kConj K5128.k64
    refine solv_C _ _ _ hs fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]
    exact pf_le_two 2 3 6 0 Nat.prime_two Nat.prime_three
  · rw [← NativeChecks.pairCountB_eq_E, pairCount_C,
      pairCount_conj QP hQP 2 4 ws (cOf pa) 192 K5128.kConj K5128.kPart, K5128.kInv]

end Certificates
