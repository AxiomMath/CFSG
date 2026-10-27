module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

@[expose] def d8Rels : List (List (Fin 7 × Bool)) :=
  j3WordsRest.filter fun r => r.all fun x => x.1.val ≤ 3

@[expose] def a2Rels : List (List (Fin 7 × Bool)) :=
  j3WordsRest.filter fun r => (r.any fun x => x.1.val == 6) && !(r.any fun x => x.1.val == 4)

@[expose] def evalWord {X : Type*} [Group X] (t : Fin 7 → X) (r : List (Fin 7 × Bool)) : X :=
  (r.map fun x => if x.2 then t x.1 else (t x.1)⁻¹).prod

@[expose] def betaTup {X : Type*} [Group X] (a2 a3 a4 s : X) : Fin 7 → X := ![1, a2, a3, a4, 1, 1, s]

@[expose] def kleinSet {X : Type*} [Group X] (c t : X) : List X := [1, c, t, c * t]

@[expose] def normSet {X : Type*} [Group X] [Fintype X] [DecidableEq X] (c t : X) : Finset X :=
  Finset.univ.filter fun g => ∀ v ∈ kleinSet c t, g * v * g⁻¹ ∈ kleinSet c t

@[expose] def centSet {X : Type*} [Group X] [Fintype X] [DecidableEq X] (c : X) : Finset X :=
  Finset.univ.filter fun x => x * c = c * x

@[expose] def BetaCheck (X : Type*) [Group X] [Fintype X] [DecidableEq X] (c0 : X) : Prop :=
  c0 * c0 = 1 ∧ c0 ≠ 1 ∧
  (∀ a : X, a * a = 1 → a ≠ 1 → ∃ g, g * c0 * g⁻¹ = a) ∧
  ∀ a2 ∈ centSet c0, ∀ a3 ∈ centSet c0,
    (∀ r ∈ d8Rels, evalWord (betaTup a2 a3 c0 1) r = 1) →
    ∃ t : X, t * t = 1 ∧ t * c0 = c0 * t ∧ t ≠ 1 ∧ t ≠ c0 ∧
      (normSet c0 t).card = 24 ∧
      (∀ x ∈ normSet c0 t, ∀ y ∈ normSet c0 t, x * y ∈ normSet c0 t) ∧
      (∀ x ∈ normSet c0 t, x⁻¹ ∈ normSet c0 t) ∧
      a2 ∈ normSet c0 t ∧ a3 ∈ normSet c0 t ∧ c0 ∈ normSet c0 t ∧
      (∀ x ∈ normSet c0 t, x ^ 3 = 1 → x ≠ 1 → ∃ u ∈ normSet c0 t, u * x * u⁻¹ = x⁻¹) ∧
      ∃ s ∈ normSet c0 t, ∀ r ∈ a2Rels, evalWord (betaTup a2 a3 c0 s) r = 1

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
instance BetaCheck.instDecidable (X : Type*) [Group X] [Fintype X] [DecidableEq X] (c0 : X) :
    Decidable (BetaCheck X c0) := by
  unfold BetaCheck
  infer_instance

end CFSG.Quasithin.Kleidman.ThreeLocal
