module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Cases
import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso
import CFSG.RankThree.PartTwo.Sec19.SimsC198Spor
import CFSG.RankThree.PartTwo.Sec19.SimsC198RankSpor

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

private theorem sporadics42_split {s : TauCeti.SporadicName} (hs : s ∈ sporadics42) :
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨
        s = .HS ∨ s = .Ru ∨ s = .He ∨ s = .J4) ∨
      (s = .J3 ∨ s = .McL ∨ s = .ONan) ∨
      (s = .Ly ∨ s = .Suz ∨ s = .Co3 ∨ s = .Co2 ∨ s = .HN ∨ s = .Th) := by
  simp only [sporadics42, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem caseHolds_six
    : CaseHolds Alt42Six := by
  intro X _ _ hX c L 𝒟 hD h
  obtain ⟨s, hs, ⟨e⟩⟩ := h
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.quasisimple.2.1
  rcases sporadics42_split hs with hs | hs | hs
  · exact absurd hD (noAutDatum_spor_small hs e c L 𝒟)
  · exact absurd hD ((noLocalDatum_spor_cent hs e).noAutDatum c L 𝒟)
  · exact (false_of_rankHyp_spor hX hs e).elim

end CFSG.RankThree.PartTwo.Sec19.SimsC198
