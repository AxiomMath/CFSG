module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6FrameDefs

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def TwE6PairOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ∀ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B → B.b = 1 →
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .twistedE6 n f p ψ R Rm ∧
      Nonempty (ExcPairData B R Rm)

@[expose] def TwE6PairTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ∀ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B → B.b = 2 →
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .twistedE6 n f p ψ R Rm ∧
      Nonempty (ExcPairData B R Rm)

theorem twE6PairSel_of_one_two (h1 : TwE6PairOne) (h2 : TwE6PairTwo) : TwE6PairSel := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos _ B hB
  rcases B.orbit with h | ⟨h, -⟩
  · exact h1 X n f ψ p G₀ B₁ D J L x hpos B hB h
  · exact h2 X n f ψ p G₀ B₁ D J L x hpos B hB h

end CFSG.StandardType.LieKnownR2.ExcPos
