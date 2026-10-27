module

public import CFSG.Models
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Models

open Assembly.LowTwoRank

variable {G G' : Type} [Group G] [Group G']

theorem LieModel.of_mulEquiv (e : G ≃* G') {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) : LieModel G' t n p f := by
  obtain ⟨hadm, hc | ⟨hn, d, hd, ⟨e'⟩⟩⟩ := h
  · exact ⟨hadm, .inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hc)⟩
  · exact ⟨hadm, .inr ⟨hn, d, hd, ⟨e.symm.trans e'⟩⟩⟩

theorem OddLieType.of_mulEquiv (e : G ≃* G') (h : OddLieType G) : OddLieType G' := by
  obtain ⟨t, n, p, f, hp, hm⟩ := h
  exact ⟨t, n, p, f, hp, hm.of_mulEquiv e⟩

theorem EvenLieType.of_mulEquiv (e : G ≃* G') (h : EvenLieType G) : EvenLieType G' := by
  obtain ⟨t, n, f, hm⟩ := h
  exact ⟨t, n, f, hm.of_mulEquiv e⟩

theorem SporadicRep.of_mulEquiv (e : G ≃* G') (h : SporadicRep G) : SporadicRep G' := by
  obtain ⟨s, ⟨e'⟩⟩ := h
  exact ⟨s, ⟨e.symm.trans e'⟩⟩

end CFSG.Models
