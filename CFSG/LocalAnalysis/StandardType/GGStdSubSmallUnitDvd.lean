module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdNorm
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdDelta
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly

section PerLabel

theorem largeEvenLabelAll_stdSubNormSmall_unitDvd {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (hl : GGUnitDvdLabelNo63 p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmall p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab hl
  obtain ⟨⟨ht, -, -, -⟩, -⟩ := hl
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hd5 hpd hpq h63 hdq
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hrank : ggUnitaryTorusRank p (l + 1) = l + 1 - 3 := by
    simp [ggUnitaryTorusRank, hpd]
  have hnd : ¬ (l + 1 = 6 ∧ p = 3) := h63
  refine ⟨K, i1, i2, hK, hQ', InndiagSU.ggOutdiagOdd_unitary hK hn (by omega) (fun he => ?_) p,
    ggUnitaryTorusRank p (l + 1), ggTorusLift_unitary hK hn (by omega) hdq hp hpq, ?_, ?_⟩
  · exact hdq (by rw [he.1, he.2])
  · rw [hrank]
    exact SmallU.ggStdSubTwoTorusNormSmall_unitDvd hK hn hd5 hp hpq hpd hnd
  · rw [hrank]
    exact SmallU.ggStdSubTwoTorusDeltaSmall_unitDvd hK hn hd5 hp hpq hpd hnd

end PerLabel

theorem ggStdSubSmallInputOn_unitDvd_holds :
    GGStdSubSmallInputOn GGUnitDvdLabelNo63 :=
  ggStdSubSmallInputOn_of_labels_normSmall ggLNoncyclicInput_holds fun _ _ hp hlab hS _ =>
    largeEvenLabelAll_stdSubNormSmall_unitDvd hp hlab hS

theorem ggStdSubSmallInputOn_of_not_unitDvd
    {T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn fun p lab => T p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) :
    GGStdSubSmallInputOn T :=
  (ggStdSubSmallInputOn_unitDvd_holds.or h).mono fun p lab hT => by
    by_cases hl : GGUnitDvdLabelNo63 p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hT, hl⟩

theorem ggStdSubSmallInputOn_rest4_of_not_unitDvd
    (h : GGStdSubSmallInputOn fun p lab =>
      GGStdSubSmallRest4Label p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) :
    GGStdSubSmallInputOn GGStdSubSmallRest4Label :=
  ggStdSubSmallInputOn_of_not_unitDvd h

@[expose] def GGStdSubSmallRest5Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGStdSubSmallRest4Label p lab ∧ ¬ GGUnitDvdLabelNo63 p lab

end CFSG.StandardType

end
