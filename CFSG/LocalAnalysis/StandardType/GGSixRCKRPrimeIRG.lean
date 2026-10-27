module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

@[expose] def RCKNormalizedModel (t : StatedLieTag) (n g : ℕ) : Prop :=
  GGPosTag t ∧ CFSG.Open.StatedLieAdmissible t n 2 g

@[expose] def RCKIntrinsicRoot :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J R Rm : Subgroup X),
    CFSG.Assembly.IsQuasisimple ↥J → Odd (Nat.card (Subgroup.center ↥J)) → GGRootPosJ J R Rm →
    (∀ (t : StatedLieTag) (n g : ℕ) (φ : (ggU t n g).K →* X), RCKNormalizedModel t n g →
      φ.range = J → φ.ker ≤ Subgroup.center (ggU t n g).K →
      ∃ (β : Fin (ggU t n g).D.rank → ℤ) (u : (ggU t n g).K), β ∈ (ggU t n g).D.roots ∧
        (GGLongRoot (ggU t n g).D β ∨
          (((t = .PSp ∧ n = 2) ∨ t = .F4) ∧ 2 • β ∉ (ggU t n g).D.roots)) ∧
        R = ggRootSub (ggU t n g).D φ β u ∧ Rm = ggRootSub (ggU t n g).D φ (-β) u) ∧
    (∀ (F : Type) [Field F] [Finite F] (σ : F →+* F) (g : ℕ) (φ : (triD4Universal F σ).K →* X),
      TriField F σ g → φ.range = J → φ.ker ≤ Subgroup.center (triD4Universal F σ).K →
      ∃ (β : Fin (triD4Universal F σ).D.rank → ℤ) (u : (triD4Universal F σ).K),
        β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β ∧
        R = ggRootSub (triD4Universal F σ).D φ β u ∧ Rm = ggRootSub (triD4Universal F σ).D φ (-β) u)

end CFSG.StandardType.RCKRP
