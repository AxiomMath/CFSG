module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAltTenGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G]

theorem eight70_le_of_normalizer_le {I X₁ X₂ A M : Subgroup G}
    (hI : Nonempty (↥I ≃* alternatingGroup (Fin 10))) (hX₁I : X₁ ≤ I) (hX₂I : X₂ ≤ I)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)))
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) (hA : A ≤ X₁) (hA3 : Nat.card A = 3)
    (hX₁M : X₁ ≤ M) (hX₂M : X₂ ≤ M) (hN : Subgroup.normalizer (A : Set G) ≤ M) : I ≤ M := by
  have hAle : A ≤ I := hA.trans hX₁I
  have h₁' : Nonempty (↥(X₁.subgroupOf I) ≃* alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hX₁I).trans h₁.some⟩
  have h₂' : Nonempty (↥(X₂.subgroupOf I) ≃* alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hX₂I).trans h₂.some⟩
  have hcomm' : ∀ x ∈ X₁.subgroupOf I, ∀ y ∈ X₂.subgroupOf I, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hcomm (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
      (Subgroup.mem_subgroupOf.mp hy)
  have hA' : A.subgroupOf I ≤ X₁.subgroupOf I := Subgroup.subgroupOf_mono I hA
  have hA3' : Nat.card ↥(A.subgroupOf I) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv]
    exact hA3
  have htop := sup_normalizer_eq_top_of_commuting_alt5 (I := ↥I) hI
    (X₁.subgroupOf I) (X₂.subgroupOf I) (A.subgroupOf I) h₁' h₂' hcomm' hA' hA3'
  have htopmap : (X₁.subgroupOf I ⊔ X₂.subgroupOf I ⊔
      Subgroup.normalizer (A.subgroupOf I : Set ↥I)).map I.subtype = I := by
    rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  have hnorm : (Subgroup.normalizer (A.subgroupOf I : Set ↥I)).map I.subtype ≤
      Subgroup.normalizer (A : Set G) := by
    have h := Subgroup.le_normalizer_map (f := I.subtype) (H := A.subgroupOf I)
    rwa [Subgroup.map_subgroupOf_eq_of_le hAle] at h
  calc I = (X₁.subgroupOf I ⊔ X₂.subgroupOf I ⊔
        Subgroup.normalizer (A.subgroupOf I : Set ↥I)).map I.subtype := htopmap.symm
    _ ≤ X₁ ⊔ X₂ ⊔ Subgroup.normalizer (A : Set G) := by
      rw [Subgroup.map_sup, Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hX₁I, Subgroup.map_subgroupOf_eq_of_le hX₂I]
      exact sup_le le_sup_left (hnorm.trans le_sup_right)
    _ ≤ M := sup_le (sup_le hX₁M hX₂M) hN

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
