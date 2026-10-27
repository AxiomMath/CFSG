module

public import CFSG.Certificates.CosetTablePresented
public import TauCeti.GroupTheory.Presentation.GroupPresentation

public section

namespace CFSG.Sporadic.Presentation

open CFSG.CosetTable TauCeti

theorem relatorSet_eq (P : GroupPresentation) :
    P.relatorSet = {r : FreeGroup (Fin P.generatorCount) | r ∈ P.relators.map FreeGroup.mk} := by
  ext r
  rw [GroupPresentation.mem_relatorSet_iff]
  simp only [Set.mem_ofPred_eq, List.mem_map, GroupPresentation.relators_def]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.toWord, ⟨t, ht, rfl⟩, Relator.toWord_toFreeGroup t⟩
  · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (Relator.toWord_toFreeGroup t).symm⟩

theorem group_card_le (P : GroupPresentation) {n : ℕ}
    (h : Finite (PG P.generatorCount P.relators) ∧ Nat.card (PG P.generatorCount P.relators) ≤ n) :
    Finite P.Group ∧ Nat.card P.Group ≤ n := by
  rw [GroupPresentation.Group, relatorSet_eq]
  exact h

theorem group_finite (P : GroupPresentation) (h : Finite (PG P.generatorCount P.relators)) :
    Finite P.Group := by
  rw [GroupPresentation.Group, relatorSet_eq]
  exact h

end CFSG.Sporadic.Presentation
