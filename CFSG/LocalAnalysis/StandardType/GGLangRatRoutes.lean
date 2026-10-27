module

public import CFSG.LocalAnalysis.StandardType.GGLangRatLocalNorm
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGLangRatNegOne
import CFSG.LocalAnalysis.StandardType.GGLangRatBCoreA
import CFSG.LocalAnalysis.StandardType.GGLangRatRouteC
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.RootAut.Count
import CFSG.HardMathSupport.Timmesfeld.Proving.SimpleRootsCartan
import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving

theorem langRatClassify
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty) :
    ∃ (t : TauCeti.DynkinType) (e : simpleRoots Ψ ≃ Fin t.rank),
      (∀ β γ : simpleRoots Ψ,
        corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ)) ∧
      (t ∈ rigidTypes ∨ (t ∈ countTypes ∧ compRank Ψ = t.rank ∧ Ψ.ncard = t.numRoots)) := by
  classical
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
    (diagramGraph_simpleRoots_connected hΨ hne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcard : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcard]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  refine ⟨t, e, he', ?_⟩
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  · exact Or.inl hmem
  · have hok : countOK t = true := List.all_eq_true.1 Certificates.certificate13659.2 t hmem
    exact Or.inr ⟨hmem, hrank, by rw [ncard_eq_ncard_orbit hΨ e he', ncard_orbit_of_orbitOK hok]⟩

theorem langRatKind_of_A_shape {τ : Tag} {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (i : KernelComponent χ) (h2 : 2 ≤ compRank (componentRoots χ i))
    (hn : (componentRoots χ i).ncard =
      compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1)) :
    twistKind ρ χ i = .inner ∨ twistKind ρ χ i = .suN := by
  unfold twistKind
  generalize compRank (componentRoots χ i) = r at *
  generalize (componentRoots χ i).ncard = N at *
  subst hn
  split_ifs with h1 h2' h3 h4
  · exact Or.inl rfl
  · exfalso
    rcases h2' with ⟨rfl, h⟩ | ⟨rfl, h, -⟩ <;> norm_num at h
  · exfalso
    obtain ⟨h4, h5⟩ := h3
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h5
    nlinarith
  · exact Or.inr rfl
  · exfalso
    exact h4 ⟨h2, rfl⟩

theorem langRatLocalNorm_holds
    (k : TwistKind) : LangRatLocalNorm k := by
  intro τ L _ _ hc2 p₀ S hτ hAlg w hn b hb i hki hqs γ hγ u r hr hwr hur
  obtain ⟨t, e, he', hcls⟩ := langRatClassify (isRootComponent_componentRoots i) ⟨γ, hγ⟩
  have hB : 2 ≤ compRank (componentRoots (rootCharHom b) i) →
      (componentRoots (rootCharHom b) i).ncard = compRank (componentRoots (rootCharHom b) i) *
        (compRank (componentRoots (rootCharHom b) i) + 1) →
      rootDiagUnit τ (∏ j ∈ Finset.range
          (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r),
        Hchar ((w ^ j) • γ) (u ^ (S.D.q ^ j))) ∈
        rationalComponent S.ρ S.Γ (rootCharHom b) i := by
    intro h2 hnc
    have hk : k = .inner ∨ k = .suN := by
      rw [← hki]
      exact langRatKind_of_A_shape S.ρ (rootCharHom b) i h2 hnc
    have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
      intro t
      rcases hτ with rfl | rfl <;> cases t <;> decide
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
    obtain ⟨hm0, hs, hmin⟩ := outer_componentOrbitLength_spec S hb i
    haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) := ⟨hm0.ne'⟩
    exact langRatFC_norm_factor_mem S hFr hΦ hn hb i hs hmin u r
      (langRatB_localCoreA k hk τ L p₀ S hτ hAlg w hn b hb i hki h2 hnc hqs γ hγ u r hr hwr hur)
  rcases hcls with hrig | ⟨hcnt, hrk, hN⟩
  · exact langRatNegOne_localNorm_of_type S hτ hAlg hn hb i e he' (Or.inl hrig) hγ u r hwr hur
  · simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hcnt
    rcases hcnt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hB (by rw [hrk]; decide) (by rw [hN, hrk]; decide)
    · exact hB (by rw [hrk]; decide) (by rw [hN, hrk]; decide)
    · exact hB (by rw [hrk]; decide) (by rw [hN, hrk]; decide)
    · exact hB (by rw [hrk]; decide) (by rw [hN, hrk]; decide)
    · exact hB (by rw [hrk]; decide) (by rw [hN, hrk]; decide)
    · exact hB (by rw [hrk]; decide) (by rw [hN, hrk]; decide)
    · exact hB (by rw [hrk]; decide) (by rw [hN, hrk]; decide)
    · exact langRatNegOne_localNorm_of_type S hτ hAlg hn hb i e he' (Or.inr (Or.inl rfl)) hγ u r
        hwr hur
    · exact langRatRouteC_localNorm_of_type S hτ hn hb i e he' (Or.inl rfl) hγ u r hwr hur
    · exact langRatNegOne_localNorm_of_type S hτ hAlg hn hb i e he'
        (Or.inr (Or.inr (Or.inl rfl))) hγ u r hwr hur
    · exact langRatRouteC_localNorm_of_type S hτ hn hb i e he' (Or.inr (Or.inl rfl)) hγ u r hwr hur
    · exact langRatNegOne_localNorm_of_type S hτ hAlg hn hb i e he'
        (Or.inr (Or.inr (Or.inr rfl))) hγ u r hwr hur
    · exact langRatRouteC_localNorm_of_type S hτ hn hb i e he' (Or.inr (Or.inr rfl)) hγ u r hwr hur

theorem langRatTorusFixedMem_holds
    : LangRatTorusFixedMem :=
  langRatTorusFixedMem_of_localNorm langRatLocalNorm_holds

end CFSG.StandardType.LangRat
