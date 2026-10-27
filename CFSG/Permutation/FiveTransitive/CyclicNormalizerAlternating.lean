module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG

namespace FiveTransitive.CyclicNormalizerAlternating

variable {G F : Type*} [Group G] (Q : Subgroup G) [IsCyclic Q]

theorem commutator_le_centralizer :
    commutator (Subgroup.normalizer (Q : Set G)) ≤
      (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)) := by
  rw [← Q.normalizerMonoidHom_ker]
  let e := IsCyclic.mulAutMulEquiv Q
  let f := e.toMonoidHom.comp Q.normalizerMonoidHom
  intro a ha
  have he : f a = 1 := Abelianization.commutator_subset_ker f ha
  apply e.injective
  simpa [f] using he

theorem exists_centralizing_lift [Fintype F] [DecidableEq F]
    (hF : 5 ≤ Nat.card F)
    (f : Subgroup.normalizer (Q : Set G) →* Equiv.Perm F)
    (hf : Function.Surjective f) (σ : Equiv.Perm F) (hσ : σ ∈ alternatingGroup F) :
    ∃ a : Subgroup.normalizer (Q : Set G),
      (a : G) ∈ Subgroup.centralizer (Q : Set G) ∧ f a = σ := by
  have hm : (commutator (Subgroup.normalizer (Q : Set G))).map f =
      alternatingGroup F := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact alternatingGroup.commutator_perm_eq hF
  rw [← hm] at hσ
  obtain ⟨a, ha, hfa⟩ := hσ
  exact ⟨a, commutator_le_centralizer Q ha, hfa⟩

theorem alternating_le_centralizer_image [Fintype F] [DecidableEq F]
    (hF : 5 ≤ Nat.card F)
    (f : Subgroup.normalizer (Q : Set G) →* Equiv.Perm F)
    (hf : Function.Surjective f) :
    alternatingGroup F ≤
      ((Subgroup.centralizer (Q : Set G)).subgroupOf
        (Subgroup.normalizer (Q : Set G))).map f := by
  intro σ hσ
  obtain ⟨a, ha, hfa⟩ := exists_centralizing_lift Q hF f hf σ hσ
  exact ⟨a, ha, hfa⟩

end FiveTransitive.CyclicNormalizerAlternating

end CFSG
