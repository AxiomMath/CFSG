module

public import CFSG.Foundations.Basic
public import CFSG.Open.Defs

import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open scoped _root_.Classical

theorem nonempty_centerQuot_a5 {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 5)) :
    Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup K := e.isSimpleGroup
  have hnc : ¬ ∀ a b : K, a * b = b * a := by
    intro h
    letI : CommGroup K := { ‹Group K› with mul_comm := h }
    have := IsSimpleGroup.prime_card (α := K)
    have h60 : Nat.card K = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card, Nat.factorial]
    rw [h60] at this
    exact absurd this (by norm_num)
  have hZ : Subgroup.center K = ⊥ := by
    rcases (inferInstance : (Subgroup.center K).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply hnc
      intro a b
      have : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

theorem openComponentOf_of_native {G : Type} [Group G] {H K : Subgroup G} (hKH : K ≤ H)
    (h : CFSG.IsComponent (K.subgroupOf H)) : CFSG.Open.IsComponentOf K H := by
  refine ⟨hKH, (CFSG.Open.IsSubnormal.iff_subgroupOf hKH).2 h.2, ?_⟩
  have h1 := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 h.1)
  exact h1.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm

theorem native_isQuasisimple_of_component {G : Type} [Group G] {H K : Subgroup G} (hKH : K ≤ H)
    (h : CFSG.IsComponent (K.subgroupOf H)) : CFSG.IsQuasisimple ↥K :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2
      (openComponentOf_of_native hKH h).2.2)

end CFSG.RankThree.PartTwo.Sec21.FF79
