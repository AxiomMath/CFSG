module

public import Mathlib.GroupTheory.Commutator.Basic

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G]

theorem le_centralizer_of_le_center {P Q X : Subgroup G}
    (hQ : Q ≤ P) (hX : X ≤ (Subgroup.center ↥P).map P.subtype) :
    Q ≤ Subgroup.centralizer (X : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hX hx)
  rw [← hzx]
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨q, hQ hq⟩)).symm

theorem commutator_eq_bot_of_le_center {P Q X : Subgroup G}
    (hQ : Q ≤ P) (hX : X ≤ (Subgroup.center ↥P).map P.subtype) :
    ⁅Q, X⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact le_centralizer_of_le_center hQ hX

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
