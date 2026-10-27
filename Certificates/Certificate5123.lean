
module

public import Certificates.Certificate5123Base

public import CFSG.GH74.KGroups.L34AutInputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import Certificates.Kernel.PermCent.K5138
import Certificates.Kernel.PermCent.KG5123A
import Certificates.Kernel.PermCent.KG5123B

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum CFSG.Certificates
  CFSG.Sporadic.Schreier

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L34 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix in
theorem certificate5123 : (QA.check = true ∧ QA.orderCertificate = 241920)
    ∧ (orderIs PA 2 = true ∧ orderIs PB 4 = true ∧ pairInvB ws PA PB = true)
    ∧ (normCheck QP QA.original.toList PA PB = true)
    ∧ (centTrivCheck (elemsT QA) PA PB = true)
    ∧ (pairCountB QP 2 4 ws = 241920) := by
  have hQP : ValidSchreier QP := check_certificate_of _ _ _ _ _ L34MT.kQP
  refine ⟨⟨check_certificate_of _ _ _ _ _ K5123.kQA.1,
    (orderCertificate_eq_orderV _).trans K5123.kQA.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [← ev_cOf PA, ← ev_cOf PB, orderIs_C, orderIs_C, pairInvB_C]
    exact K5123.kOrd
  · rw [← map_cOf_ev QA.original.toList, ← ev_cOf PA, ← ev_cOf PB, norm_C]
    exact K5123.kNorm
  · rw [elemsT_eq_elemsC, ← ev_cOf PA, ← ev_cOf PB, centTriv_C]
    exact K5123.kCent
  · rw [pairCount_C, pairCount_conj QP hQP 2 4 ws (cOf PA) 768 K5123.kConj K5123.kPart,
      K5123.kInv]

end Certificates
