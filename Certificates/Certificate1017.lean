module

public import Certificates.Certificate1016Base
public import Certificates.Kernel.Sporadic.Fi24Fix.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24 in
theorem certificate1017 : ∃ Γ : Subgroup (GL (Fin 781) (ZMod 3)),
    (∀ g : GL (Fin 781) (ZMod 3), g.val = mA ∨ g.val = mB → g ∈ Γ) ∧
    ∀ P : Fin 306936 → Submodule (ZMod 3) (Fin 781 → ZMod 3), Function.Injective P →
      (∀ k, ∃ g ∈ Γ, P k = (pt 0).sp.map
        (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3)))) →
      ∃ Ψ : Finset (Fin 306936), Ψ.card = 31671 ∧ (∀ k ∈ Ψ, P k ≠ (pt 0).sp) ∧
        (∀ g ∈ Γ, (pt 0).sp.map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) =
            (pt 0).sp →
          ∀ k ∈ Ψ, ∃ k' ∈ Ψ,
            (P k).map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) = P k') ∧
        (Ψ.filter fun k => (P k).map (Matrix.mulVecLin mA) = P k).card = 360 := KernelFi24Fix.certificate1017_proof

end Certificates

end
