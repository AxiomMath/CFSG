module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownDefs

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGTwE6OfOutsideAt (lab : LargeEvenLabel) : Prop :=
  LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    Finite R →
    ∀ (s t : MulAut R) (n : ℕ), s ^ 3 = 1 → t ^ 3 = 1 → s * t = t * s → s ∈ I → t ∈ I →
      3 ∣ 2 ^ n + 1 →
      ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
        LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
          lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
            lab' = ⟨.twA, 2, 3 * n⟩) →
        GGOutsideInndiag J₁ t →
        (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ GGTorusLift 3 5 R

@[expose] def GGTwE6A5LAt (lab : LargeEvenLabel) : Prop :=
  LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    Finite R →
    ∀ (B' : Subgroup (MulAut R)) (s : MulAut R) (n : ℕ), IsElemAbelian 3 B' →
      (∀ a ∈ B', a ∈ I) → s ∈ B' → s ≠ 1 → 3 ^ 4 ≤ Nat.card B' → 3 ∣ 2 ^ n + 1 →
      ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) → (∀ a ∈ B', ∀ m ∈ J₁, a m ∈ J₁) →
        LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) →
        GGUnitaryCommLifts J₁ n 6 (B' : Set (MulAut R)) ∨
          (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ GGTorusLift 3 5 R

theorem ggTwE6OfOutsideAt_of_torusLift {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R) : GGTwE6OfOutsideAt lab :=
  fun Q hQ => largeEvenRawDatum_mono
    (fun _ _ _ _ hq => ⟨hq.1, by dsimp only; intros; exact Or.inr hq.2⟩) (h Q hQ)

theorem ggTwE6A5LAt_of_torusLift {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R) : GGTwE6A5LAt lab :=
  fun Q hQ => largeEvenRawDatum_mono
    (fun _ _ _ _ hq => ⟨hq.1, by dsimp only; intros; exact Or.inr (Or.inr hq.2)⟩) (h Q hQ)

@[expose] def GGNoThreeCenter (lab : LargeEvenLabel) : Prop :=
  match lab.tag with
  | .A => ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n - 1)
  | .twA => ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1)
  | .E6 => ¬ 3 ∣ 2 ^ lab.n - 1
  | .twE6 => ¬ 3 ∣ 2 ^ lab.n + 1
  | _ => True

end CFSG.StandardType.SCFourCover

end
