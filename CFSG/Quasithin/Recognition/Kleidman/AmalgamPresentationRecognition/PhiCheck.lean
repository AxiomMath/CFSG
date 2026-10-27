module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.SplitPhi

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

@[expose] def evalWordC {X : Type*} [Group X] (e : Fin 7 → X) (r : List (Fin 7 × Bool)) : X :=
  (r.map fun x => cond x.2 (e x.1) (e x.1)⁻¹).prod

@[expose] def PhiC (X : Type*) [Group X] : Prop :=
  ∀ b₂ b₃ b₄ : X, b₂ * b₂ = 1 → b₃ * b₃ = 1 → b₄ * b₄ = 1 → b₄ ≠ 1 →
    (∀ r ∈ relsD8, evalWordC (tupQ b₂ b₃ b₄ 1) r = 1) →
    ∃ c t : X, c ^ 3 = 1 ∧ t * t = 1 ∧ t * c * t = c⁻¹ ∧
      (∀ p ∈ [b₃, b₄], c * p * c⁻¹ ∈ kleinList b₃ b₄ ∧ t * p * t⁻¹ ∈ kleinList b₃ b₄) ∧
      (∀ v ∈ kleinList b₃ b₄, ∀ i < 3, ∀ j < 2, v * c ^ i * t ^ j = 1 → v = 1 ∧ i = 0 ∧ j = 0) ∧
      (∃ v ∈ kleinList b₃ b₄, ∃ i < 3, ∃ j < 2, b₂ = v * c ^ i * t ^ j) ∧
      ∃ v ∈ kleinList b₃ b₄, ∃ i < 3, ∃ j < 2,
        ∀ r ∈ relsA2, evalWordC (tupQ b₂ b₃ b₄ (v * c ^ i * t ^ j)) r = 1

theorem PhiC_iff (X : Type*) [Group X] : PhiC X ↔ Phi X := Iff.rfl

set_option synthInstance.maxSize 4096 in
instance PhiC.decidable (X : Type*) [Group X] [Fintype X] [DecidableEq X] : Decidable (PhiC X) := by
  unfold PhiC
  infer_instance

instance Phi.decidable (X : Type*) [Group X] [Fintype X] [DecidableEq X] : Decidable (Phi X) :=
  decidable_of_iff (PhiC X) (PhiC_iff X)

@[expose] def PhiM (X : Type*) [Group X] (I C : Multiset X) : Prop :=
  ∀ b₂ ∈ I, ∀ b₃ ∈ I, ∀ b₄ ∈ I, b₄ ≠ 1 →
    (∀ r ∈ relsD8, evalWordC (tupQ b₂ b₃ b₄ 1) r = 1) →
    ∃ c ∈ C, ∃ t ∈ I, t * c * t = c⁻¹ ∧
      (∀ p ∈ [b₃, b₄], c * p * c⁻¹ ∈ kleinList b₃ b₄ ∧ t * p * t⁻¹ ∈ kleinList b₃ b₄) ∧
      (∀ v ∈ kleinList b₃ b₄, ∀ i < 3, ∀ j < 2, v * c ^ i * t ^ j = 1 → v = 1 ∧ i = 0 ∧ j = 0) ∧
      (∃ v ∈ kleinList b₃ b₄, ∃ i < 3, ∃ j < 2, b₂ = v * c ^ i * t ^ j) ∧
      ∃ v ∈ kleinList b₃ b₄, ∃ i < 3, ∃ j < 2,
        ∀ r ∈ relsA2, evalWordC (tupQ b₂ b₃ b₄ (v * c ^ i * t ^ j)) r = 1

local instance (priority := high) multisetForall {X : Type*} {M : Multiset X} {p : X → Prop}
    [∀ a, Decidable (p a)] : Decidable (∀ a ∈ M, p a) :=
  Multiset.decidableForallMultiset

local instance (priority := high) multisetExists {X : Type*} {M : Multiset X} {p : X → Prop}
    [DecidablePred p] : Decidable (∃ a ∈ M, p a) :=
  Multiset.decidableExistsMultiset

set_option synthInstance.maxSize 4096 in
instance PhiM.decidable (X : Type*) [Group X] [DecidableEq X] (I C : Multiset X) :
    Decidable (PhiM X I C) := by
  unfold PhiM
  infer_instance

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
