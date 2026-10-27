module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.NativeSporadic (IsSporadic)

@[expose] def K335SporNormAt (n : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSporadic X n →
    ∀ S Q : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ → Q ≤ S → Nat.card Q = 9 →
      ∃ g ∈ Subgroup.normalizer (S : Set X), ∃ x ∈ Q, g⁻¹ * x * g ∉ Q

theorem k335SporadicNormalizer_of_at (hM24 : K335SporNormAt .M24) (hJ2 : K335SporNormAt .J2)
    (hHe : K335SporNormAt .He) (hRu : K335SporNormAt .Ru) (hJ4 : K335SporNormAt .J4) :
    K335SporadicNormalizer := by
  intro X _ _ h
  rcases h with h | h | h | h | h
  exacts [hM24 X h, hJ2 X h, hHe X h, hRu X h, hJ4 X h]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
