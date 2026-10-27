
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8DataInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2014K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup in
theorem facts2014 : (admCheck (elemsT QS8) QA8 five8 s8 admConj = true)
    ∧ (QL8.check = true ∧ QL8.orderCertificate = 360)
    ∧ (oddNormalCheck (elemsT QL8) 45 = true)
    ∧ (((elemsT QA8).filter (fun g => decide (g * s8 = s8 * g))).length = 720)
    ∧ (QQ8.check = true ∧ QQ8.orderCertificate = 32)
    ∧ ((elemsT QQ8).all (fun q => QQ8.sift (g08 * q * g08⁻¹) 0) = true ∧
      QQ8.sift g08 0 = false ∧ QQ8.sift (g08 * g08) 0 = true
    )
    ∧ (((elemsT QS8).filter (fun g => decide (g * s8 = s8 * g))).length = 2 ^ 5 * 45) := by
  refine ⟨?_, ql8_2014K, ?_, ?_, qq8_2014K, ?_, ?_⟩
  · unfold admCheck five8
    simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact adm2014K
  · rw [elemsT_eq_elemsV]
    exact oddNormal2014K
  · rw [elemsT_eq_elemsV]
    exact cA2014K
  · rw [elemsT_eq_elemsV]
    exact g08_2014K
  · rw [elemsT_eq_elemsV]
    exact cS2014K

end CertificateChecks.KernelCatFacts
