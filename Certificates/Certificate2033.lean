module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadStabilizer
import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22PointStabilizer
import Certificates.Certificate2195
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexInputs
import Certificates.Kernel.LocalComp.WittA2033
import Certificates.Certificate2195

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction in
open scoped Pointwise in
theorem certificate2033 : ((∀ x, ofTable zTab x = (CFSG.Sporadic.Mathieu.m22gA * CFSG.Sporadic.Mathieu.m22gB) x) ∧
      (∀ j : Fin 11, ∀ x, ofTable zPowTabs[j.val]! x = (ofTable zTab)^[j] x) ∧
      (∀ j : Fin 5, ∀ x, ofTable wPowTabs[j.val]! x = (ofTable wTab)^[j] x) ∧
      (∀ j : Fin 7, ∀ x, ofTable yPowTabs[j.val]! x = (ofTable yTab)^[j] x) ∧
      (∀ x, (ofTable wTab)^[5] x = x) ∧ ofTable wTab 0 ≠ 0 ∧
      (∀ x, (ofTable yTab)^[7] x = x) ∧ ofTable yTab 0 ≠ 0 ∧
      (∀ x, ofTable wTab (ofTable zTab x) = ofTable zPowTabs[9]! (ofTable wTab x)) ∧
      (∀ x, ofTable cTab (ofTable wTab x) = ofTable wPowTabs[2]! (ofTable cTab x))
    )
    ∧ (m22Count (fun g => ∀ x, g x = ofTable wTab x) = 1 ∧
      m22Count (fun g => ∀ x, g x = ofTable cTab x) = 1 ∧
      m22Count (fun g => ∀ x, g x = ofTable yTab x) = 1
    )
    ∧ (m22Count (fun f => ∃ j : Fin 11, ∀ x, f (ofTable zTab x) = ofTable zPowTabs[j.val]! (f x)) =
        55 ∧
      m22Count (fun f => ∃ j : Fin 5, ∀ x, f (ofTable wTab x) = ofTable wPowTabs[j.val]! (f x)) =
        20 ∧
      m22Count (fun f => ∃ j : Fin 7, ∀ x, f (ofTable yTab x) = ofTable yPowTabs[j.val]! (f x)) =
        21
    ) := KernelLC.Witt.facts2033

end Certificates
