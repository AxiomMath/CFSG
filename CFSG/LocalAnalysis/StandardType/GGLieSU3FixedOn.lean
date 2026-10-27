module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGLabelSUFour (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 3)

@[expose] def GGLieSU3FixedInputOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGAutLocal A δ J →
      Subgroup.center J ≠ ⊥ →
      LargeEvenMarking X (fun lab _ _ I _ θ =>
        GGLabelTwClassical lab ∧ S lab ∧ GGInducedInn A θ I) →
      LargeEvenMarking J (fun lab' _ _ _ _ _ => GGLabelA2 lab' ∧ lab'.tag = .twA) →
        ¬ GGAutsFixedInCenter A J

theorem ggLieSU3FixedInput_of_split (S : LargeEvenLabel → Prop)
    (h₁ : GGLieSU3FixedInputOn S) (h₂ : GGLieSU3FixedInputOn fun lab => ¬ S lab) :
    GGLieSU3FixedInput := by
  intro X _ _ hX A δ J hl hZ hm hJ
  have hm' : LargeEvenMarking X (fun lab _ _ I _ θ =>
      (GGLabelTwClassical lab ∧ S lab ∧ GGInducedInn A θ I) ∨
      (GGLabelTwClassical lab ∧ ¬ S lab ∧ GGInducedInn A θ I)) :=
    largeEvenMarking_mono (fun lab R _ I F θ h => by
      by_cases hS : S lab
      · exact Or.inl ⟨h.1, hS, h.2⟩
      · exact Or.inr ⟨h.1, hS, h.2⟩) hm
  rcases largeEvenMarking_or hm' with h | h
  · exact h₁ X hX A δ J hl hZ h hJ
  · exact h₂ X hX A δ J hl hZ h hJ

end CFSG.StandardType
