module

public import CFSG.Sporadic.Schreier.Co1TernaryCodeInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
import Certificates.Kernel.SporSch.Co1.Tern

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix in
theorem certificate2149 : (∀ n < 13,
      (Finset.univ.filter fun b : Fin 6 → ZMod 3 => (tsupp (b ᵥ* R)).card = n).card =
        weightCount n
    )
    ∧ (sixSupports.card = 132 ∧
      ∀ F ∈ (Finset.univ : Finset (Fin 12)).powersetCard 5,
        (sixSupports.filter fun s => F ⊆ s).card = 1
    ) :=
  ⟨KernelSporSch.Co1Tern.weights, KernelSporSch.Co1Tern.supports⟩

end Certificates
