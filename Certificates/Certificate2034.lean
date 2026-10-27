module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCasesInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndex
import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndex
import Certificates.Certificate2037
import Certificates.Certificate2038
import Certificates.Certificate2195
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCasesInputs
import Certificates.Kernel.LocalComp.WittA2034
import Certificates.Certificate2195

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction in
open scoped Pointwise in
theorem certificate2034 : (∀ x, ofTable wTab (ofTable zTab (ofTable zTab (ofTable wTab (ofTable cTab
      (ofTable zTab (ofTable wTab (ofTable cTab (ofTable cTab (ofTable cTab (ofTable zTab
      (ofTable wTab (ofTable cTab x)))))))))))) =
        List.formPerm [0, 12] (List.formPerm [1, 7] (List.formPerm [2, 15] (List.formPerm [3, 11]
          (List.formPerm [5, 21] (List.formPerm [6, 16] (List.formPerm [8, 9]
            (List.formPerm [10, 13] x)))))))
    )
    ∧ ((∀ z, ofTable yTab z = z ↔ z = 4) ∧
      (∀ z, ofTable wTab z = z ↔ z = 8 ∨ z = 12)
    )
    ∧ (∀ z : Fin 22, z ≠ 4 →
      (Finset.univ.image fun k : Fin 7 => (ofTable yTab)^[k] z) ∈ [orbY1, orbY2, orbY3]
    )
    ∧ (orbY1.card = 7 ∧ orbY2.card = 7 ∧ orbY3.card = 7)
    ∧ (m22Count (fun f => ∀ x ∈ orbY1, f x ∈ orbY1) = 2520 ∧
      m22Count (fun f => ∀ x ∈ orbY2, f x ∈ orbY2) = 168 ∧
      m22Count (fun f => ∀ x ∈ orbY3, f x ∈ orbY3) = 2520
    )
    ∧ (m22Count InP2 = 128 ∧ m22Count (fun f => InP2 f ∧ f 0 = 0) = 64 ∧
      m22Count (fun f => InP2 f ∧ f 2 = 2) = 32 ∧ m22Count (fun f => InP2 f ∧ f 3 = 3) = 8 ∧
      m22Count (fun f => ∀ x ∈ pairX2, f x ∈ pairX2) = 1920
    ) := KernelLC.Witt.facts2034

end Certificates
