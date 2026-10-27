module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.W4Local
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.DichotomyLetters

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Quasithin.Kleidman.ThreeLocal

theorem mem_collapseRels_or_of_mem_dichotomyRelators {r : List (Fin 7 × Bool)}
    (hr : r ∈ dichotomyRelators) : r ∈ collapseRels ∨ r = wRelator 4 0 ∨ r = wRelator 4 1 := by
  have : ∀ r ∈ dichotomyRelators, r ∈ collapseRels ∨ r = wRelator 4 0 ∨ r = wRelator 4 1 := by
    decide +kernel
  exact this r hr

theorem dichotomy_cases {X : Type*} [Group X] (ρ : Fin 7 → X)
    (hrel : ∀ r ∈ j3WordsRest, FreeGroup.lift ρ (FreeGroup.mk r) = 1)
    {r : List (Fin 7 × Bool)} (hr : r ∈ dichotomyRelators)
    (h : FreeGroup.lift ρ (FreeGroup.mk r) = 1) :
    ρ 6 ∈ Subgroup.closure (ρ '' {i : Fin 7 | i.val < 6}) ∨ r = wRelator 4 0 ∨
      r = wRelator 4 1 := by
  rcases mem_collapseRels_or_of_mem_dichotomyRelators hr with hc | h0 | h1
  · left
    have := e6_mem_closure_of_collapse hc ρ hrel h
    have hset : {i : Fin 7 | i.val ≠ 6} = {i : Fin 7 | i.val < 6} := by
      ext i; simp only [Set.mem_setOf_eq]; have := i.2; omega
    rwa [hset] at this
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr h1)

theorem card_closure_le_rels40 {X : Type*} [Group X]
    (ρ : Fin 7 → X)
    (h : ∀ r ∈ j3WordsRest ++ [wRelator 4 0], FreeGroup.lift ρ (FreeGroup.mk r) = 1) :
    Nat.card (Subgroup.closure (Set.range ρ)) ≤ 315 * 1920 :=
  card_closure_le_J2 ρ h

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
