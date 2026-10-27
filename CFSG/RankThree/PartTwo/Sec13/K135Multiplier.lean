module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverCert
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem kFactMultiplier_holds :
    KFactMultiplier := by
  intro Q _ _ hQ h
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hQ
      (X := CFSG.Blueprint.NativeSporadic.Carrier .He) e
    have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (CFSG.Blueprint.NativeSporadic.Carrier .He)) = 1 := nativeRow_He
    rw [h2] at h1
    exact h1.trans (one_dvd 3)
  · obtain ⟨e⟩ := h
    have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hQ
      (X := CFSG.Blueprint.NativeSporadic.Carrier .ONan) e
    rwa [ONCover.nativeRow_ONan] at h1
  · obtain ⟨e⟩ := h
    have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hQ
      (X := CFSG.Blueprint.NativeSporadic.Carrier .J4) e
    have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (CFSG.Blueprint.NativeSporadic.Carrier .J4)) = 1 := nativeRow_J4
    rw [h2] at h1
    exact h1.trans (one_dvd 3)

end CFSG.RankThree.PartTwo.Sec13.F135Last
