module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SyncFree
public import CFSG.LocalAnalysis.StandardType.GGReeB2SyncRun

public section

namespace CFSG.StandardType.ReeB2Fixed

theorem IM_holds (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) : IM e := by
  intro A B hI hadm
  by_cases h : ∃ p, SyncAt e A B p
  · obtain ⟨p, hp⟩ := h
    exact exists_slots_of_syncAt e he h3 A B hI hadm.2.2 p hp
  · exact absurd hadm.2.2 (not_disjoint_of_syncFree e he h3 A B hI (by simpa using h))

end CFSG.StandardType.ReeB2Fixed
