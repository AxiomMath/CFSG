module

public import CFSG.LocalAnalysis.StandardType.GGSixExcPosRangeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLPos
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4Forms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2F4Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2F4NC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E6Root
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E6NC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E7Root
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E8Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E8NC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Root
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6ShortRoot
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Conj

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

theorem itemTwo_of_thmSRangeAt
    {X : Type} [Group X] [Finite X] {K R : Subgroup X} (h : GGThmSRangeAt K R) :
    GGRootInnerAt K R ∧ GGRootNoCentralAt K R := by
  unfold GGThmSRangeAt at h
  rcases h with
      ⟨m, g, β, hdim, hβ, φ, hφ, hker, u, hR⟩
    | ⟨n, g, β, hn, hnf, hβ, hpos, φ, hφ, hker, u, hR⟩
    | ⟨n, g, β, hadm, hβ, φ, hφ, hker, u, hR⟩
    | ⟨n, g, β, hn, hβ, φ, hφ, hker, u, hR⟩
    | ⟨n, g, β, hn, hβ, hl, φ, hφ, hker, u, hR⟩
    | ⟨F, hField, hFinite, σ, g, β, hF, hl, φ, hφ, hker, u, hR⟩
    | ⟨t, g, β, ht, hg, hβ, φ, hφ, hker, u, hR⟩
    | ⟨g, β, hβ, hlen, φ, hφ, hker, u, hR⟩
  · rw [← hφ]
    exact PSL.itemTwo_ggU_psl (k := m) hdim φ hker hβ u hR
  · rw [← hφ, hR]
    exact ⟨PSU.ggRootInnerAt_ggU_psu hn hnf φ hker hβ hpos u,
      PSU.ggRootNoCentralAt_ggU_psu hn hnf φ hker hβ hpos u⟩
  · rw [← hφ, hR]
    exact ⟨PSp.ggRootInnerAt_ggU_psp (n := n) (f := g) hadm.2.2.1 φ hker hβ u,
      PSp.ggRootNoCentralAt_ggU_psp hadm φ hker hβ u⟩
  · rw [← hφ, hR]
    exact ⟨POmega.ggRootInnerAt_ggU_pomegaPlus hn φ hker hβ u,
      POmega.ggRootNoCentralAt_ggU_pomegaPlus hn φ hker hβ u⟩
  · rw [← hφ, hR]
    exact ⟨POmega.ggRootInnerAt_ggU_pomegaMinus hn φ hker hβ hl u,
      POmega.ggRootNoCentralAt_ggU_pomegaMinus hn φ hker hβ hl u⟩
  · letI : Field F := hField
    letI : Finite F := hFinite
    rw [← hφ, hR]
    exact ⟨TriD4.ggRootInnerAt_triD4 hF φ hker hl u,
      TriD4.ggRootNoCentralAt_triD4 hF φ hker hl u⟩
  · rcases ht with rfl | rfl | rfl | rfl
    · rw [← hφ, hR]
      exact ⟨F4.ggRootInnerAt_ggU_f4 hg φ hker hβ u,
        F4.ggRootNoCentralAt_ggU_f4 φ hker hβ u⟩
    · rw [← hφ, hR]
      exact ⟨E6.ggRootInnerAt_ggU_e6 hg φ hker hβ u,
        E6.ggRootNoCentralAt_ggU_e6 φ hker hβ u⟩
    · rw [← hφ, hR]
      exact ⟨E7.ggRootInnerAt_ggU_e7 hg φ hker hβ u,
        E7.ggRootNoCentralAt_ggU_e7 φ hker hβ u⟩
    · rw [← hφ, hR]
      exact ⟨E8.ggRootInnerAt_ggU_e8 hg φ hker hβ u,
        E8.ggRootNoCentralAt_ggU_e8 φ hker hβ u⟩
  · rcases hlen with ⟨hg, hl⟩ | ⟨hg, hs⟩
    · rw [← hφ, hR]
      exact ⟨TwE6.ggRootInnerAt_ggU_twistedE6_long hg φ hker hl u,
        TwE6.ggRootNoCentralAt_ggU_twistedE6_long hg φ hker hl u⟩
    · obtain ⟨w, hw⟩ := Short.twE6_exists_weyl_of_not_long
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 g) hβ hs
      rw [← hφ, hR]
      exact ⟨TwE6.ggRootInnerAt_ggU_twistedE6_short hg φ hker ⟨w, hw⟩ u,
        TwE6.ggRootNoCentralAt_ggU_twistedE6_short hg φ hker ⟨w, hw⟩ u⟩

theorem ggSixLieKnownPos_E6_of_explicit
    (h : GGSixExcPosExplicit .E6) : GGSixLieKnownPos .E6 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hH : GGSixPosHyp .E6 n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hcases⟩ := h X n f ψ p G₀ B₁ D J L x hH
  obtain ⟨β₀, hβ₀, -, u₀, hR₀, -⟩ := id hpos0
  have hf : 1 ≤ f := h3.admissible.2.1
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    rcases hcases e he hene K hKG hKcomp hJK hKne hKodd with hKG₀ | hrange
    · rw [hKG₀, ← h1, hR₀]
      exact ⟨E6.ggRootInnerAt_ggU_e6 hf ψ h2 hβ₀ u₀,
        E6.ggRootNoCentralAt_ggU_e6 ψ h2 hβ₀ u₀⟩
    · exact itemTwo_of_thmSRangeAt hrange
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    exact E6.itemThree_ggU_e6 hf ψ h2 hβ₀ u₀ hR₀ Y hY hYnorG hYnorR hcomm

theorem ggSixLieKnownPos_E7_of_explicit
    (h : GGSixExcPosExplicit .E7) : GGSixLieKnownPos .E7 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hH : GGSixPosHyp .E7 n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hcases⟩ := h X n f ψ p G₀ B₁ D J L x hH
  obtain ⟨β₀, hβ₀, -, u₀, hR₀, -⟩ := id hpos0
  have hf : 1 ≤ f := h3.admissible.2.1
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    rcases hcases e he hene K hKG hKcomp hJK hKne hKodd with hKG₀ | hrange
    · rw [hKG₀, ← h1, hR₀]
      exact ⟨E7.ggRootInnerAt_ggU_e7 hf ψ h2 hβ₀ u₀,
        E7.ggRootNoCentralAt_ggU_e7 ψ h2 hβ₀ u₀⟩
    · exact itemTwo_of_thmSRangeAt hrange
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    exact E7.itemThree_ggU_e7 hf ψ h2 hβ₀ u₀ hR₀ Y hY hYnorG hYnorR hcomm

theorem ggSixLieKnownPos_E8_of_explicit
    (h : GGSixExcPosExplicit .E8) : GGSixLieKnownPos .E8 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hH : GGSixPosHyp .E8 n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hcases⟩ := h X n f ψ p G₀ B₁ D J L x hH
  obtain ⟨β₀, hβ₀, -, u₀, hR₀, -⟩ := id hpos0
  have hf : 1 ≤ f := h3.admissible.2.1
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    rcases hcases e he hene K hKG hKcomp hJK hKne hKodd with hKG₀ | hrange
    · rw [hKG₀, ← h1, hR₀]
      exact ⟨E8.ggRootInnerAt_ggU_e8 hf ψ h2 hβ₀ u₀,
        E8.ggRootNoCentralAt_ggU_e8 ψ h2 hβ₀ u₀⟩
    · exact itemTwo_of_thmSRangeAt hrange
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    exact E8.itemThree_ggU_e8 hf ψ h2 hβ₀ u₀ hR₀ Y hY hYnorG hYnorR hcomm

theorem ggSixLieKnownPos_twistedE6_of_explicit
    (h : GGSixExcPosExplicit .twistedE6) : GGSixLieKnownPos .twistedE6 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hH : GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  have hf : 1 ≤ f := h3.admissible.2.1
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hcases⟩ := h X n f ψ p G₀ B₁ D J L x hH
  obtain ⟨β₀, hβ₀, hls₀, u₀, hR₀, -⟩ := id hpos0
  have hf2_of_not_long : ¬ GGLongRoot (ggU .twistedE6 n f).D β₀ → 2 ≤ f := by
    intro hl
    have hpdiv : p ∣ 2 ^ f - 1 := by
      rcases (hls₀.resolve_left hl).1 with hcase | hcase | hcase
      · exact absurd hcase (by decide)
      · exact absurd hcase (by decide)
      · exact hcase.2
    by_contra hf2'
    have hf1 : f = 1 := by omega
    subst hf1
    have hpdvd1 : p ∣ 1 := by simpa using hpdiv
    have hple1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hpdvd1
    have hp2 : 2 ≤ p := h5.two_le
    omega
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    rcases hcases e he hene K hKG hKcomp hJK hKne hKodd with hKG₀ | hrange
    · rw [hKG₀, ← h1, hR₀]
      by_cases hl : GGLongRoot (ggU .twistedE6 n f).D β₀
      · exact ⟨TwE6.ggRootInnerAt_ggU_twistedE6_long hf ψ h2 hl u₀,
          TwE6.ggRootNoCentralAt_ggU_twistedE6_long hf ψ h2 hl u₀⟩
      · have hf2 := hf2_of_not_long hl
        obtain ⟨w, hw⟩ := Short.twE6_exists_weyl_of_not_long
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hβ₀ hl
        exact ⟨TwE6.ggRootInnerAt_ggU_twistedE6_short hf2 ψ h2 ⟨w, hw⟩ u₀,
          TwE6.ggRootNoCentralAt_ggU_twistedE6_short hf2 ψ h2 ⟨w, hw⟩ u₀⟩
    · exact itemTwo_of_thmSRangeAt hrange
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    by_cases hl : GGLongRoot (ggU .twistedE6 n f).D β₀
    · exact TwE6.itemThree_ggU_twistedE6_long hf ψ h2 hl u₀ hR₀ Y hY hYnorG hYnorR hcomm
    · have hf2 := hf2_of_not_long hl
      obtain ⟨w, hw⟩ := Short.twE6_exists_weyl_of_not_long
        (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hβ₀ hl
      exact TwE6.itemThree_ggU_twistedE6_short hf2 ψ h2 ⟨w, hw⟩ u₀ hR₀ Y hY hYnorG hYnorR
        hcomm

end CFSG.StandardType.LieKnownR2
