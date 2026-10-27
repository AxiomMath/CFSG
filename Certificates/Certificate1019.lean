module

import Certificates.Kernel.Sporadic.Fi24Fix.FinalA
public import CFSG.Sporadic.Fi24.OrbitBase
public import Certificates.Certificate1016Base

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24 in
theorem certificate1019 : ∃ Γ : Subgroup (GL (Fin 781) (ZMod 3)),
    (∀ g : GL (Fin 781) (ZMod 3), g.val = mA ∨ g.val = mB → g ∈ Γ) ∧
    ∀ P : Fin 306936 → Submodule (ZMod 3) (Fin 781 → ZMod 3), Function.Injective P →
      (∀ k, ∃ g ∈ Γ, P k = (pt 0).sp.map
        (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3)))) →
      ∃ Ψ : Finset (Fin 306936), Ψ.card = 31671 ∧ (∀ k ∈ Ψ, P k ≠ (pt 0).sp) ∧
        (∀ g ∈ Γ, (pt 0).sp.map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) =
            (pt 0).sp →
          ∀ k ∈ Ψ, ∃ k' ∈ Ψ,
            (P k).map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) = P k') ∧
        ∃ k ∈ Ψ, P k = (pt 0).sp.map (Matrix.mulVecLin mA) := KernelFi24Fix.certificate1019_proof

end Certificates

end
