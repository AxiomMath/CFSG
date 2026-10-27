module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.RCKSmall (RCKSmallTag RCKSmallLabel RCKSmallEmpty)
open CFSG.StandardType.RCKA6 (RCKLemmaP)

private theorem rckGB_labelTag_of_rowA6 {lab : LargeEvenLabel}
    (h : ggSixRCKLabelRow lab = .A6) : lab.tag = .B2der := by
  cases h' : lab.tag <;> simp only [ggSixRCKLabelRow, h'] at h ⊢ <;>
    (try split_ifs at h) <;> simp_all

private theorem rckGB_quot_A6
    {X : Type} [Group X] {J : Subgroup X} (hrow : GGSixRCKJRow .A6 J) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨lab, _hlab, R, _hR, I, F, θ, _hsimple, _hna, hP, hmodel⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have htag : lab.tag = .B2der := rckGB_labelTag_of_rowA6 hP
  obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der htag hmodel
  exact ⟨θ.trans e⟩

theorem ggSixRootCommKnownRow_IV_of_smallEmpty
    (hS : RCKSmallEmpty) :
    GGSixRootCommKnownRow .IV := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hJ hpres hO hp hp2 hA hB₁A hDB₁ hD hAN hc1 hB₁N hB₁J
    hB₁ hSC hrk hAG₀ hB₁L hHL hJc hZ hLG₀ hLx hDL hJL hA6
  refine (hS X t n f ψ p G₀ A B₁ D J L ?_ hpres hO hp hp2 hA hB₁A hDB₁ hD hAN hc1 hB₁N hB₁J
    hB₁ hSC hrk hAG₀ hB₁L hHL hJc hZ hLG₀ hLx hDL hJL hA6).elim
  obtain ⟨hc, lab, hlab, hraw⟩ := hJ
  refine ⟨hc, lab, hlab,
    CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, h⟩ => ⟨hs, hna, θ, ?_⟩) hraw⟩
  rcases lab with ⟨tag, rank, m⟩
  cases tag <;> simp [CFSG.StandardType.ggSixRCKLabelRow, RCKSmallTag] at h ⊢ <;>
    split_ifs at h

theorem ggSixRootCommKnownRow_A6_of_lemmaP
    (hP : RCKLemmaP) : GGSixRootCommKnownRow .A6 := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hJ hpres hO hp hp2 hA hB₁A hDB₁ hD hAN hc1 hB₁N hB₁J
    hB₁ hSC hrk hAG₀ hB₁L hHL hJc hZ hLG₀ hLx hDL hJL hA6
  have hZJ : Subgroup.center ↥J = ⊥ :=
    hP X t n f ψ p G₀ A D J hpres hp hp2 hA (hDB₁.trans hB₁A) hD hAN hc1 hJc hZ hJ
  obtain ⟨e⟩ := rckGB_quot_A6 hJ
  exfalso
  exact hA6.false (((QuotientGroup.quotientMulEquivOfEq hZJ).trans
    QuotientGroup.quotientBot).symm.trans e)

end CFSG.StandardType.RCKC1
