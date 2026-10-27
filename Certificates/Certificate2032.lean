module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22InvolutionsInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
import Certificates.Certificate2195
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22InvolutionsInputs
import Certificates.Kernel.LocalComp.WittA2032
import Certificates.Certificate2195

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction in
open CFSG.Sporadic.Mathieu in
theorem certificate2032 : (m22Count (fun g => ∀ x, g x = aFun x) = 1)
    ∧ (m22Count (fun g => ∀ x, g (aFun x) = aFun (g x)) = 384)
    ∧ ((∀ x, aFun (aFun x) = x) ∧ aFun 0 ≠ 0) := KernelLC.Witt.facts2032

end Certificates
