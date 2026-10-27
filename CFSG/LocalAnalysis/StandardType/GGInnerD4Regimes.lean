module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGInnerOnD4On (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X),
    IsElemAbelian 3 A → σ ∈ A → IsComponentOf J (ggAutFixedSubgroup σ) →
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
    LargeEvenMarking X (fun lab _ _ I _ θ => S lab ∧ GGInducedInn A θ I) →
    ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ → labJ.tag = .D → labJ.rank = 4 →
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → ∀ a ∈ A, ∃ u ∈ J, ∀ v ∈ J, a v = u * v * u⁻¹

theorem GGInnerOnD4On.mono {S S' : LargeEvenLabel → Prop} (hSS' : ∀ lab, S lab → S' lab)
    (h : GGInnerOnD4On S') : GGInnerOnD4On S := by
  intro X _ _ A σ J hA hσ hJ hN hmark labJ hΛ htag hrk hlab a ha
  refine h X A σ J hA hσ hJ hN ?_ labJ hΛ htag hrk hlab a ha
  exact largeEvenMarking_mono (fun lab R _ I F θ ⟨hs, hi⟩ => ⟨hSS' lab hs, hi⟩) hmark

theorem GGInnerOnD4On.union {S₁ S₂ : LargeEvenLabel → Prop} (h₁ : GGInnerOnD4On S₁)
    (h₂ : GGInnerOnD4On S₂) : GGInnerOnD4On fun lab => S₁ lab ∨ S₂ lab := by
  intro X _ _ A σ J hA hσ hJ hN hmark labJ hΛ htag hrk hlab a ha
  obtain ⟨hX, lab, hlab', hraw⟩ := hmark
  obtain ⟨R, _, I, F, -, -, θ, hS, -⟩ := largeEvenRawDatum_exists hraw
  rcases hS with hs | hs
  · refine h₁ X A σ J hA hσ hJ hN ⟨hX, lab, hlab', largeEvenRawDatum_mono ?_ hraw⟩ labJ hΛ htag hrk
      hlab a ha
    rintro R' _ I' F' ⟨hsimp, hna, θ', -, hi⟩
    exact ⟨hsimp, hna, θ', hs, hi⟩
  · refine h₂ X A σ J hA hσ hJ hN ⟨hX, lab, hlab', largeEvenRawDatum_mono ?_ hraw⟩ labJ hΛ htag hrk
      hlab a ha
    rintro R' _ I' F' ⟨hsimp, hna, θ', -, hi⟩
    exact ⟨hsimp, hna, θ', hs, hi⟩

end CFSG.StandardType

end
