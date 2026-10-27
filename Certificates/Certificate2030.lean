module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadStabilizerInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
import Certificates.Certificate2195
import Certificates.Certificate2031
import Certificates.Certificate2035
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadStabilizerInputs
import Certificates.Kernel.LocalComp.WittA2030
import Certificates.Certificate2195

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction in
open scoped Pointwise in
theorem certificate2030 : (m22Count (fun g => ∀ x ∈ hexad0, g x = x) = 16)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ ∀ x, g (g x) = x) = 16)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ g 3 = 3) = 1)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadD0, g x ∈ hexadD0) = 360)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadT0, g x ∈ hexadT0) = 96)
    ∧ (hexadD0 ∈ hexadList)
    ∧ (hexadT0 ∈ hexadList)
    ∧ ((hexad0 ∩ hexadD0).card = 0)
    ∧ ((hexad0 ∩ hexadT0).card = 2) := KernelLC.Witt.facts2030

end Certificates
