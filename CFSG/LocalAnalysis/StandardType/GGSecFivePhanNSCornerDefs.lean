module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary

@[expose] def GGSecFiveNSCornerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (f : ℕ) (ψ : Su K 2 f 6 →* G), GGNSLocalHyp p B Bs K f 6 ψ → p = 3 →
      ∀ b₁ ∈ Bs, ∀ b₂ ∈ Bs, ∀ g₁ g₂ : GL (Fin 6) K,
        GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁ → GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂ →
          g₁ * g₂ = g₂ * g₁

end CFSG.StandardType

end
