module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGTwE6OfOutsideSplitKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (s t : MulAut L') (n : ℕ), s ^ 3 = 1 → t ^ 3 = 1 → s * t = t * s →
          (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (s l)) → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (t l)) →
          3 ∣ 2 ^ n + 1 →
          ∀ J₁ : Subgroup L', IsComponentOf J₁ (ggFix s) →
            LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
              lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
                lab' = ⟨.twA, 2, 3 * n⟩) →
            GGOutsideInndiag J₁ t →
            (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ GGTorusLift 3 5 R

end CFSG.StandardType

end
