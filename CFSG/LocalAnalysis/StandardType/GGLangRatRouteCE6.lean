module

public import CFSG.LocalAnalysis.StandardType.GGLangRatRouteCCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriKac
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

theorem langRatRouteC_e6_pinned
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8) {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b))
    (hrank : compRank (componentRoots (rootCharHom b) i) = 6)
    (hcard : (componentRoots (rootCharHom b) i).ncard = 72) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom b) i =
      (fun α => v • α) '' parabolicRoots τ (CFSG.RankThree.PartOne.KE6.e6Nodes τ) := by
  obtain ⟨N, hN, hNL, hTN⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_exists_order S hb
  rcases hτ with rfl | rfl
  · obtain ⟨v, μ, -, hpinned⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_exists_pinned_of_pos hN hNL
        CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_E7 hTN
    obtain ⟨x, C, -, -, hi, hr, hc⟩ := hpinned i
    have hC := CFSG.HardMathSupport.Timmesfeld.LangTorus.kacCount_E7_six C (hr ▸ hrank)
      (hc ▸ hcard)
    subst hC
    refine ⟨v, ?_⟩
    rw [hi, CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.rootsOf_eq_parabolicRoots _
      (by decide)]
    congr 2
    ext j
    simp only [Set.mem_setOf_eq, CFSG.RankThree.PartOne.KE6.e6Nodes]
    fin_cases j <;> decide
  · obtain ⟨v, μ, -, hpinned⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_exists_pinned_of_pos hN hNL
        CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_E8 hTN
    obtain ⟨x, C, -, -, hi, hr, hc⟩ := hpinned i
    have hC := CFSG.HardMathSupport.Timmesfeld.LangTorus.kacCount_E8_six C (hr ▸ hrank)
      (hc ▸ hcard)
    subst hC
    refine ⟨v, ?_⟩
    rw [hi, CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.rootsOf_eq_parabolicRoots _
      (by decide)]
    congr 2
    ext j
    simp only [Set.mem_setOf_eq, CFSG.RankThree.PartOne.KE6.e6Nodes]
    fin_cases j <;> decide

theorem langRatRouteC_modelPerfect_e6
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8) {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b))
    (hrank : compRank (componentRoots (rootCharHom b) i) = 6)
    (hcard : (componentRoots (rootCharHom b) i).ncard = 72) :
    Group.IsPerfect ↥(rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model) := by
  obtain ⟨v, hv⟩ := langRatRouteC_e6_pinned S hτ hb i hrank hcard
  have h5 : 5 ≤ compRank (componentRoots (rootCharHom b) i) := by omega
  rcases hτ with rfl | rfl
  · obtain ⟨D⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedData_of_e6Class S hb i v hv
    exact langRatRouteC_modelPerfect_of_fixedData S hb i h5 D
  · obtain ⟨D⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedData_of_e6Class S hb i v hv
    exact langRatRouteC_modelPerfect_of_fixedData S hb i h5 D

end CFSG.StandardType.LangRat

end
