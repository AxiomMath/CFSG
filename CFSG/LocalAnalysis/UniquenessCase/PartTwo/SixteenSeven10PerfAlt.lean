module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c1610_center_of_isAlt {Y : Type} [Group Y] {n : ℕ} (hn : 4 ≤ n)
    (h : UC22.IsAlt Y n) : Subgroup.center Y = ⊥ := by
  obtain ⟨e⟩ := h
  have hA : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using hn)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hA, Subgroup.mem_bot] at hz'
  exact e.injective (by rw [hz', map_one])

theorem s16c1610_commutator_of_isAlt {Y : Type} [Group Y] {n : ℕ} (hn : 5 ≤ n)
    (h : UC22.IsAlt Y n) : _root_.commutator Y = ⊤ := by
  obtain ⟨e⟩ := h
  have hA : ⁅(⊤ : Subgroup (alternatingGroup (Fin n))), (⊤ : Subgroup (alternatingGroup (Fin n)))⁆ =
      ⊤ := commutator_alternatingGroup_eq_top (by simpa using hn)
  have h1 : (⁅(⊤ : Subgroup (alternatingGroup (Fin n))),
      (⊤ : Subgroup (alternatingGroup (Fin n)))⁆).map e.symm.toMonoidHom =
      ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.symm.surjective]
  show ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤
  rw [← h1, hA, Subgroup.map_top_of_surjective _ e.symm.surjective]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
