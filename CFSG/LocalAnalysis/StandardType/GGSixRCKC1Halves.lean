module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Helpers

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.RCKSmall (RCKSmallTag RCKSmallLabel RCKSmallEmpty)

theorem ggSixRootCommKnownRow_of_halves
    (i : GGSixRCKRow) (Pos : RCKPos)
    (h1 : RCKRowK1 i Pos) (h2 : RCKRowK2 i Pos) : GGSixRootCommKnownRow i := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hJrow hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN hBC h4
    hsc hrank hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6
  obtain ⟨rb, Vb, hK1Data, hPos⟩ := h1 ↥J hZ hJrow
  have hK1Data0 := hK1Data
  obtain ⟨hrbVb, hrb1, hVb, hVb4, hconj, hK1b⟩ := hK1Data
  obtain ⟨V, r, hrV, hVJ, hVab, hV4, hrC, hconjV, ⟨r', hr'_eq, hr'_π⟩, hVmap, hK1'⟩ :=
    K1Lift.lemmaK hJc.2.2 hZ hrbVb hrb1 hVb hVb4 hconj hK1b
  refine ⟨V, r, hrV, hVJ, hVab, hV4, hrC, hconjV, ?_, ?_⟩
  · intro Y hY hYL hYNJ hYD hYr hYnorm v hv y hy
    exact hK1' Y hY hYNJ hYr hYnorm v hv y hy
  · have hK2 := h2 X t n f ψ p G₀ A B₁ D J L hJrow hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN
      hBC h4 hsc hrank hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6 rb Vb hK1Data0 hPos V r'
      (by simpa only [hr'_eq] using hrV) hVJ hVab hV4 hr'_π hVmap
      (by simpa only [hr'_eq] using hconjV) (by simpa only [hr'_eq] using hK1')
    rw [← hr'_eq]
    exact hK2

theorem ggSixRootCommKnownRow_of_halves_ns
    (i : GGSixRCKRow) (Pos : RCKPos)
    (h1 : RCKRowK1NS i Pos) (h2 : RCKRowK2 i Pos) (hS : RCKSmallEmpty) :
    GGSixRootCommKnownRow i := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hJrow hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN hBC h4
    hsc hrank hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hJrow
  by_cases hsmall : RCKSmallTag lab.tag
  ·
    exact (hS X t n f ψ p G₀ A B₁ D J L
      ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F hq => ⟨hq.1, hq.2.1, ⟨hq.2.2.choose, hsmall⟩⟩) hraw⟩
      hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN hBC h4 hsc hrank hAC hBL hmkL hJc hZ hLG hLx
      hDL hJL hA6).elim
  ·
    have hJrowNS : LargeEvenMarking ↥J
        (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = i ∧ ¬ RCKSmallTag lab.tag) :=
      ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F hq => ⟨hq.1, hq.2.1, ⟨hq.2.2.choose, hq.2.2.choose_spec, hsmall⟩⟩) hraw⟩
    have hJrow0 : GGSixRCKJRow i J := ⟨hcomm, lab, hlab, hraw⟩
    obtain ⟨rb, Vb, hK1Data, hPos⟩ := h1 ↥J hZ hJrowNS
    have hK1Data0 := hK1Data
    obtain ⟨hrbVb, hrb1, hVb, hVb4, hconj, hK1b⟩ := hK1Data
    obtain ⟨V, r, hrV, hVJ, hVab, hV4, hrC, hconjV, ⟨r', hr'_eq, hr'_π⟩, hVmap, hK1'⟩ :=
      K1Lift.lemmaK hJc.2.2 hZ hrbVb hrb1 hVb hVb4 hconj hK1b
    refine ⟨V, r, hrV, hVJ, hVab, hV4, hrC, hconjV, ?_, ?_⟩
    · intro Y hY hYL hYNJ hYD hYr hYnorm v hv y hy
      exact hK1' Y hY hYNJ hYr hYnorm v hv y hy
    · have hK2 := h2 X t n f ψ p G₀ A B₁ D J L hJrow0 hpres hodd hp hp2 hA hBA hDB hD hAN hmk hBN
        hBC h4 hsc hrank hAC hBL hmkL hJc hZ hLG hLx hDL hJL hA6 rb Vb hK1Data0 hPos V r'
        (by simpa only [hr'_eq] using hrV) hVJ hVab hV4 hr'_π hVmap
        (by simpa only [hr'_eq] using hconjV) (by simpa only [hr'_eq] using hK1')
      rw [← hr'_eq]
      exact hK2

end CFSG.StandardType.RCKC1
