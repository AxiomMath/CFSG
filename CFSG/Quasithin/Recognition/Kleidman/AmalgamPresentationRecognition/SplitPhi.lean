module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.A2Check
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.HRelatorsModel

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

@[expose] def tupQ {X : Type*} [Group X] (b₂ b₃ b₄ b : X) : Fin 7 → X := ![1, b₂, b₃, b₄, 1, 1, b]

@[expose] def kleinList {X : Type*} [Group X] (b₃ b₄ : X) : List X := [1, b₃, b₄, b₃ * b₄]

@[expose] def Phi (X : Type*) [Group X] : Prop :=
  ∀ b₂ b₃ b₄ : X, b₂ * b₂ = 1 → b₃ * b₃ = 1 → b₄ * b₄ = 1 → b₄ ≠ 1 →
    (∀ r ∈ relsD8, evalWord (tupQ b₂ b₃ b₄ 1) r = 1) →
    ∃ c t : X, c ^ 3 = 1 ∧ t * t = 1 ∧ t * c * t = c⁻¹ ∧
      (∀ p ∈ [b₃, b₄], c * p * c⁻¹ ∈ kleinList b₃ b₄ ∧ t * p * t⁻¹ ∈ kleinList b₃ b₄) ∧
      (∀ v ∈ kleinList b₃ b₄, ∀ i < 3, ∀ j < 2, v * c ^ i * t ^ j = 1 → v = 1 ∧ i = 0 ∧ j = 0) ∧
      (∃ v ∈ kleinList b₃ b₄, ∃ i < 3, ∃ j < 2, b₂ = v * c ^ i * t ^ j) ∧
      ∃ v ∈ kleinList b₃ b₄, ∃ i < 3, ∃ j < 2,
        ∀ r ∈ relsA2, evalWord (tupQ b₂ b₃ b₄ (v * c ^ i * t ^ j)) r = 1

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
