module

public import CFSG.Sporadic.HNSchreier.Involution
import Certificates.Kernel.W4RowLane.HNGlue

public section

namespace Certificates

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
theorem certificate1037101 : (∃ u g₁ g₂ h₁ h₂ : JH, u ^ 2 = 1 ∧ u ≠ 1 ∧ ¬IsConj aJ u ∧
      orderOf (aJ * (g₁ * aJ * g₁⁻¹) * (g₂ * aJ * g₂⁻¹)) = 19 ∧
      orderOf (u * (h₁ * u * h₁⁻¹) * (h₂ * u * h₂⁻¹)) = 19) ∧
    ∃ w : JH,
      orderOf (cU * ((w : GL (Fin hnsData.d) (ZMod 5)) * cU *
        (w : GL (Fin hnsData.d) (ZMod 5))⁻¹)) = 19 :=
  ⟨CFSG.KD.W4RowLane.HN.hn_inner, CFSG.KD.W4RowLane.HN.hn_outer⟩

end Certificates
