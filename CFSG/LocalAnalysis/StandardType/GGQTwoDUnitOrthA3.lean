module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

@[expose] def QTwoOrthAdjA3Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Bs Y : Subgroup G), CFSG.Open.IsElemAbelian 3 Bs →
    ∀ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 → 5 ≤ Φ.r →
      Subgroup.center ↥Y = ⊥ →
        ∀ r₁ ∈ ggAutomizer Y Bs, GGIsReflection 3 r₁ → ∀ r₂ ∈ ggAutomizer Y Bs,
          GGIsReflection 3 r₂ → ∀ r₃ ∈ ggAutomizer Y Bs, GGIsReflection 3 r₃ →
            r₁ * r₂ ≠ r₂ * r₁ → r₂ * r₃ ≠ r₃ * r₂ → r₁ * r₃ = r₃ * r₁ → r₁ ≠ r₃ →
              ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G,
                θ.range = ggRankTwoIn Y Bs r₁ r₂ ⊔ ggRankTwoIn Y Bs r₂ r₃

end CFSG.StandardType.QTwo

end
