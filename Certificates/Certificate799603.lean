module

public import Certificates.Kernel.F4Levi.Final

@[expose] public section

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.SeitzReduction.F4Pilot

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.SeitzReduction.F4Pilot in
theorem certificate799603 :     ∀ x₁ ∈ (C3Levi (ZMod 2) : Subgroup F42C), ∀ x₂ ∈ (C3Levi (ZMod 2) : Subgroup F42C),
      IsConj rAE x₁ → IsConj rAE x₂ → ∃ l ∈ (C3Levi (ZMod 2) : Subgroup F42C), l * x₁ * l⁻¹ = x₂ :=
  CFSG.KC.F4Levi.fusion_kc

end Certificates
