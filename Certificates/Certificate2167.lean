module

public import CFSG.Sporadic.Schreier.J1VecCheckInputs
import Certificates.Kernel.SporSch.J1.Vec2167

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.ProperTwoGeneratedCore Matrix in
theorem certificate2167 : (J1Certificate.vectors.Nodup)
    ∧ (∀ i : Fin 3080, j1Vec i ≠ 0)
    ∧ (∀ i : Fin 3080, j1_first_matrix *ᵥ j1Vec i = j1Vec (j1Idx j1A1List i))
    ∧ (∀ i : Fin 3080, j1_second_matrix *ᵥ j1Vec i = j1Vec (j1Idx j1A2List i))
    ∧ (j1BasisMat * j1BasisInv = 1) := KernelSporSch.J1.vecFacts

end Certificates
