module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

@[expose] def powW (u : List (Fin 7 × Bool)) (n : ℕ) : List (Fin 7 × Bool) :=
  (List.replicate n u).flatten

@[expose] def wW : List (Fin 7 × Bool) := [(5, true), (6, true), (5, false), (6, false), (3, true)]

@[expose] def gW : List (Fin 7 × Bool) := [(5, true), (6, true)]

@[expose] def wRel (o k : ℕ) : List (Fin 7 × Bool) := powW wW o ++ List.replicate k (0, false)

@[expose] def gRel (o k : ℕ) : List (Fin 7 × Bool) := powW gW (2 * o) ++ List.replicate k (0, false)

@[expose] def collapseRels : List (List (Fin 7 × Bool)) :=
  ([3, 5].flatMap fun o => [0, 1, 2].map fun k => wRel o k) ++ [wRel 4 2] ++
    ([3, 4].flatMap fun o => [0, 1, 2].map fun k => gRel o k)

@[expose] def j3WordsW : List (List (Fin 7 × Bool)) := j3WordsRest ++ [wRel 4 1]

@[expose] def j2Words : List (List (Fin 7 × Bool)) := j3WordsRest ++ [wRel 4 0]

@[expose] def SatisfiesJ3WordsW {X : Type*} [Group X] (ρ : Fin 7 → X) : Prop :=
  ∀ r ∈ j3WordsW, FreeGroup.lift ρ (FreeGroup.mk r) = 1

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
