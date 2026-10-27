module

public import CFSG.Sporadic.Schreier.Co1SignedMono
public import CFSG.Sporadic.Schreier.Co1ElemThreeSigned
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open CFSG.Sporadic.Mathieu CFSG.Blueprint

namespace CertificateChecks.Batch2146

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open CFSG.Sporadic.Mathieu CFSG.Blueprint

private theorem sign_check_0 : ∀ b : Fin 6 → ZMod 3, (∀ j, (b ᵥ* R) j ≠ 0) →
    (∀ k, R *ᵥ ((b ᵥ* R) * R k) = 0) → b ᵥ* R = 1 ∨ b ᵥ* R = -1 := by
  decide +kernel

end CertificateChecks.Batch2146

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix in
open CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate2146 : ∀ b : Fin 6 → ZMod 3, (∀ j, (b ᵥ* R) j ≠ 0) →
    (∀ k, R *ᵥ ((b ᵥ* R) * R k) = 0) → b ᵥ* R = 1 ∨ b ᵥ* R = -1 := by
  exact CertificateChecks.Batch2146.sign_check_0

end Certificates
