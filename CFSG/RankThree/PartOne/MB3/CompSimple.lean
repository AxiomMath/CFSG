module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup
open scoped commutatorElement

variable {T : Type} [Group T]

theorem ne_bot_of_isQuasisimple {E : Subgroup T} (hE : CFSG.IsQuasisimple E) : E ≠ ⊥ := by
  intro h
  have hsub : Subsingleton ↥E := by
    rw [h]
    infer_instance
  have hss : Subsingleton (↥E ⧸ Subgroup.center ↥E) :=
    Function.Surjective.subsingleton (QuotientGroup.mk'_surjective (Subgroup.center ↥E))
  have hnt := hE.2.1.toNontrivial
  exact not_nontrivial_iff_subsingleton.mpr hss hnt

theorem eq_of_isComponent {S E : Subgroup T} (hS : IsSimpleGroup ↥S)
    (hcomm : ∀ x y : T, ⁅x, y⁆ ∈ S) (hE : CFSG.IsComponent E) : E = S := by
  have hperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp hE.1.1
  have hES : E ≤ S := by
    rw [← hperf, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  rcases (hE.2.subgroupOf (K := S)).eq_bot_or_top_of_isSimpleGroup hS with h | h
  · exfalso
    apply ne_bot_of_isQuasisimple hE.1
    rw [eq_bot_iff]
    intro x hx
    have hxS : (⟨x, hES hx⟩ : S) ∈ E.subgroupOf S := hx
    rw [h] at hxS
    simpa using hxS
  · refine le_antisymm hES fun x hx => ?_
    have : (⟨x, hx⟩ : S) ∈ E.subgroupOf S := by
      rw [h]
      exact Subgroup.mem_top _
    exact this

theorem not_isComponent_of_commute (hcomm : ∀ x y : T, x * y = y * x) {E : Subgroup T} :
    ¬ CFSG.IsComponent E := by
  intro hE
  have hperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp hE.1.1
  have hbot : E = ⊥ := by
    rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
    intro x _ y _
    have := hcomm x y
    rw [Subgroup.mem_bot, commutatorElement_def]
    simp [this]
  exact ne_bot_of_isQuasisimple hE.1 hbot

end CFSG.RankThree.PartOne.MB3
