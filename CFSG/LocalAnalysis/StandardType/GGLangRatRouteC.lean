module

public import CFSG.LocalAnalysis.StandardType.GGLangRatRouteCTwoD
public import CFSG.LocalAnalysis.StandardType.GGLangRatRouteCInnerD
public import CFSG.LocalAnalysis.StandardType.GGLangRatRouteCE6

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

theorem langRatRouteC_localNorm_of_type
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {t : TauCeti.DynkinType}
    (e : simpleRoots (componentRoots (rootCharHom b) i) ≃ Fin t.rank)
    (he' : ∀ β γ : simpleRoots (componentRoots (rootCharHom b) i),
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ))
    (ht : t = .D 5 ∨ t = .D 7 ∨ t = .E6)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom b) i) (u : Lˣ) (r : ℕ)
    (hwr : (w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) • γ = γ)
    (hur : u ^ (S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) = u) :
    rootDiagUnit τ (∏ j ∈ Finset.range
        (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r),
      Hchar ((w ^ j) • γ) (u ^ S.D.q ^ j)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom b) i := by
  classical
  have hΨ : IsRootComponent (componentRoots (rootCharHom b) i) := isRootComponent_componentRoots i
  have hcardΔ : (simpleRoots (componentRoots (rootCharHom b) i)).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank (componentRoots (rootCharHom b) i) = t.rank := by
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, hcardΔ]
  have hmem : t ∈ CFSG.HardMathSupport.Timmesfeld.RootAut.countTypes := by
    rcases ht with rfl | rfl | rfl <;> simp [CFSG.HardMathSupport.Timmesfeld.RootAut.countTypes]
  have hok : CFSG.HardMathSupport.Timmesfeld.RootAut.countOK t = true :=
    List.all_eq_true.1 Certificates.certificate13659.2 t hmem
  have hN : (componentRoots (rootCharHom b) i).ncard = t.numRoots := by
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.ncard_eq_ncard_orbit hΨ e he',
      CFSG.HardMathSupport.Timmesfeld.RootAut.ncard_orbit_of_orbitOK hok]
  have h5 : 5 ≤ compRank (componentRoots (rootCharHom b) i) := by
    rw [hrank]
    rcases ht with rfl | rfl | rfl <;> decide
  have hD : ∀ {n : ℕ}, t = .D n → 5 ≤ n → n ≠ 6 →
      Group.IsPerfect ↥(rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model) := by
    intro n htn hn5 hn6
    subst htn
    simp only [TauCeti.DynkinType.rank_D] at hrank
    simp only [TauCeti.DynkinType.numRoots_D] at hN
    by_cases hinner : twistInner (componentRoots (rootCharHom b) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom b) i)])
    · exact langRatRouteC_modelPerfect_innerD S hb i e (fun β γ => by
        rw [he', TauCeti.DynkinType.cartanMatrix_D,
          ← CFSG.LieType.Universal.Spin.cartanD_eq]
        rfl) hn5 hinner
    · have hkind : twistKind S.ρ (rootCharHom b) i = .twoD := by
        unfold twistKind
        rw [if_neg hinner, if_neg (by rw [hrank]; rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega),
          if_pos ⟨by omega, by rw [hN, hrank]⟩]
      exact langRatRouteC_modelPerfect_twoD S hb i hkind h5
  have hperf : Group.IsPerfect
      ↥(rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model) := by
    rcases ht with ht | ht | ht
    · exact hD ht (by decide) (by decide)
    · exact hD ht (by decide) (by decide)
    · subst ht
      exact langRatRouteC_modelPerfect_e6 S hτ hb i (by rw [hrank]; rfl) (by rw [hN]; rfl)
  exact langRatRouteC_localNorm_of_modelPerfect S hτ hn hb i h5 hperf hγ u r hwr hur

end CFSG.StandardType.LangRat

end
