module

public import CFSG.Sporadic.Schreier.Co1ElemThreeData

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix

namespace CertificateChecks.Batch16017

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix

private theorem find?_eq_self_0 :
    ∀ k : Fin 12, (List.finRange 12).find? (fun i => decide (i = k)) = some k := by
  decide +kernel

end CertificateChecks.Batch16017

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix in
theorem certificate16017 : ∀ k : Fin 12, (List.finRange 12).find? (fun i => decide (i = k)) = some k := by
  exact CertificateChecks.Batch16017.find?_eq_self_0

end Certificates
