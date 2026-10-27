module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityLift
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriality

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open

theorem oddTranspListExtTriality_of_cases (hD : OddTranspositionListInputClsDerivedEq)
    (h4 : ExtTrialityOrthPlusFour) (hO : ExtTrialityOrthOther) (hN : ExtTrialityNonOrth) :
    OddTranspListExtTriality := by
  intro X _ _ s hord hodd hncl hO2 hOZ hE
  obtain ⟨M, hMn, hM, huniq, hMs, hcent, hidx, hW, hcls, -⟩ := hE
  have hset : ExtSetting (X ⧸ Subgroup.center X) (QuotientGroup.mk s) M :=
    ⟨setup_quotient_center hodd hncl hO2, eq_bot_of_normal_isSolvable_quotient_center hO2 hOZ,
      hM, huniq, hMs, hcent, hidx, hW, hcls⟩
  have hL := extLiftData_extLift hord hodd hncl hO2 hOZ hM hMs hcent hcls
  rcases oddTranspListAlt_extLift hD hord hodd hncl hO2 hOZ hM hMs hcent hcls with
    ⟨m, n, hSp | hU | hOr | hWr⟩ | ⟨n, hSym⟩ | h63 | h79 | ⟨n, hn, hSz⟩
  · exact (hN _ _ _ hset _ _ hL (Or.inl ⟨m, n, Or.inl hSp⟩)).elim
  · exact (hN _ _ _ hset _ _ hL (Or.inl ⟨m, n, Or.inr (Or.inl hU)⟩)).elim
  · rcases isOrthReflection_iff.mp hOr with ⟨k, hk, -, hP⟩ | ⟨k, hk, -, hMi⟩
    · by_cases hk4 : k = 4
      · subst hk4
        exact Or.inr (h4 _ _ _ hset _ _ n hL hP)
      · exact (hO _ _ _ hset _ _ n hL (Or.inl ⟨k, hk, hk4, hP⟩)).elim
    · exact (hO _ _ _ hset _ _ n hL (Or.inr ⟨k, hk, hMi⟩)).elim
  · exact (hN _ _ _ hset _ _ hL (Or.inl ⟨m, n, Or.inr (Or.inr hWr)⟩)).elim
  · exact (hN _ _ _ hset _ _ hL (Or.inr (Or.inl ⟨n, hSym⟩))).elim
  · exact (hN _ _ _ hset _ _ hL (Or.inr (Or.inr (Or.inl h63)))).elim
  · exact Or.inl (oddTranspListAlt_of_sevenNine_le _ h79)
  · exact (hN _ _ _ hset _ _ hL (Or.inr (Or.inr (Or.inr ⟨n, hn, hSz⟩)))).elim

end CFSG.OddTranspositions.PartFour
