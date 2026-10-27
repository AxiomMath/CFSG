module

public import CFSG.Sporadic.Fi22.Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenInputs
import Certificates.Kernel.Fi22Gen.Subsets

public section

namespace Certificates

open CertificateChecks

open scoped Pointwise in
theorem certificate25270 : ∀ S S' : Finset (Fin 3510),
    S ⊆ (Finset.univ.filter fun y : Fin 3510 =>
      y.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted) →
    S' ⊆ (Finset.univ.filter fun y : Fin 3510 =>
      y.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted) →
    S.card = S'.card → S.card ≤ 3 →
    ∃ x : CFSG.Sporadic.Fi22.J,
      x • (Finset.univ.filter fun y : Fin 3510 =>
        y.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted) =
        (Finset.univ.filter fun y : Fin 3510 =>
          y.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted) ∧ x • S = S' :=
  fun S S' hS hS' hc h3 => KernelFi22Gen.subsets_trans S S' hS hS' hc h3

end Certificates
