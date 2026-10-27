
module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8PermInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2019K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.GSThmB.A8 CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GSThmB in
open CFSG.ComponentClassification.GSThmB.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.CatFactsSmall.A8 in
theorem facts2019 : (tauCheck (elemsT QA8) t15 = true)
    ∧ (n3Check (elemsT QL8) QL8 n3Data = true)
    ∧ (n4Check (elemsT QS8) (elemsT QA8) t15 = true) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [elemsT_eq_elemsV]
  · exact tau2019K
  · exact n3_2019K
  · exact n4_2019K

end CertificateChecks.KernelCatFacts
