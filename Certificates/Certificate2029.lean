module

public import Certificates.Certificate2038
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsInputs

public section

open CFSG.ComponentClassification.WittDesign

namespace CertificateChecks.Batch2029

open CFSG.ComponentClassification.WittDesign

theorem hexad0_card_0 : hexad0.card = 6 := by
  decide +kernel

example : ¬ hexad0.card = 5 := by
  decide +kernel

end CertificateChecks.Batch2029

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction in
open scoped Pointwise in
theorem certificate2029 : hexad0.card = 6 := CertificateChecks.Batch2029.hexad0_card_0

end Certificates
