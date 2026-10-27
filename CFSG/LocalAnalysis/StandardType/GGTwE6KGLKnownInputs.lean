module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLBridgeDefs

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGInndiagOnCompKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → 3 ∣ 2 ^ lab.n + 1 → GGNoThreeCenter lab →
    lab.tag ≠ .E7 → lab.tag ≠ .E8 → lab.tag ≠ .twB2 → lab.tag ≠ .B2der →
    lab.tag ≠ .G2der → lab.tag ≠ .twF4der →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R →
      ∀ (s t : MulAut R) (n : ℕ), s ^ 3 = 1 → s ≠ 1 → t ^ 3 = 1 → s * t = t * s → s ∈ I →
        t ∈ I → 3 ∣ 2 ^ n + 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
            lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
              lab' = ⟨.twA, 2, 3 * n⟩) →
          ¬ GGOutsideInndiag J₁ t

@[expose] def GGUnitaryCubicKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → 3 ∣ 2 ^ lab.n + 1 → lab.tag = .twA →
    (lab.rank = 2 ∨ lab.rank = 5) → ¬ GGNoThreeCenter lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R →
      ∀ (s t : MulAut R) (n : ℕ), s ^ 3 = 1 → s ≠ 1 → t ^ 3 = 1 → s * t = t * s → s ∈ I →
        t ∈ I → 3 ∣ 2 ^ n + 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
            lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
              lab' = ⟨.twA, 2, 3 * n⟩) →
          ¬ GGOutsideInndiag J₁ t

end CFSG.StandardType.SCFourCover

end
