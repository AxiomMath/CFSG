module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import Certificates.Kernel.PermCent.KG5137
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.PkCV.L216T

namespace Certificates

private theorem e4_eq : ((elemsT QA).all fun g => !decide (g * g = 1) ||
    invP.any fun u => decide (g * u = u * g) &&
      invP.any fun v => decide (v ≠ u) && decide (g * v = v * g) && decide (u * v = v * u)) =
    e4C := by
  unfold invP e4C invC
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, List.filter_map]
  simp only [List.all_map, List.any_map, Function.comp_def, ne_eq, decide_not, ev_mul', eq_one_ev,
    decide_ev_eq, comm_fast]

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Uniqueness in
open CFSG.GH74.Uniqueness.SU in
open CFSG.GH74.Uniqueness.SU.K in
open CFSG.GH74.Uniqueness.SU.K.R4 in
open CFSG.GH74.Uniqueness.SU.K.R4.L216M in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Matrix in
theorem certificate5137 : (CFSG.GH74.Uniqueness.SU.K.R4.L216M.QP.check = true ∧ CFSG.GH74.Uniqueness.SU.K.R4.L216M.QP.orderCertificate = 4080)
    ∧ (CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA.check = true ∧ CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA.orderCertificate = 16320)
    ∧ (orderIs CFSG.GH74.Uniqueness.SU.K.R4.L216M.pa 2 = true ∧ orderIs CFSG.GH74.Uniqueness.SU.K.R4.L216M.pb 3 = true ∧ pairInvB CFSG.GH74.Uniqueness.SU.K.R4.L216M.ws CFSG.GH74.Uniqueness.SU.K.R4.L216M.pa CFSG.GH74.Uniqueness.SU.K.R4.L216M.pb = true)
    ∧ (normCheck CFSG.GH74.Uniqueness.SU.K.R4.L216M.QP CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA.original.toList CFSG.GH74.Uniqueness.SU.K.R4.L216M.pa CFSG.GH74.Uniqueness.SU.K.R4.L216M.pb = true)
    ∧ (centTrivCheck (elemsT CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA) CFSG.GH74.Uniqueness.SU.K.R4.L216M.pa CFSG.GH74.Uniqueness.SU.K.R4.L216M.pb = true)
    ∧ (((elemsT CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA).all fun g => !decide (g * g = 1) ||
    invP.any fun u => decide (g * u = u * g) &&
      invP.any fun v => decide (v ≠ u) && decide (g * v = v * g) && decide (u * v = v * u)) =
    true)
    ∧ (pairCountB CFSG.GH74.Uniqueness.SU.K.R4.L216M.QP 2 3 CFSG.GH74.Uniqueness.SU.K.R4.L216M.ws = 16320) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ K5137.kQP.1,
    (orderCertificate_eq_orderV _).trans K5137.kQP.2⟩,
    ⟨check_certificate_of _ _ _ _ _ K5137.kQA.1, (orderCertificate_eq_orderV _).trans K5137.kQA.2⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ev_cOf pa, ← ev_cOf pb, orderIs_C, orderIs_C, pairInvB_C]
    exact K5137.kOrd
  · rw [← map_cOf_ev QA.original.toList, ← ev_cOf pa, ← ev_cOf pb, norm_C]
    exact K5137.kNorm
  · rw [elemsT_eq_elemsC, ← ev_cOf pa, ← ev_cOf pb, centTriv_C]
    exact K5137.kCent
  · rw [e4_eq]
    exact K5137.kE4
  · rw [pairCount_C]
    exact K5137.kCount

end Certificates
