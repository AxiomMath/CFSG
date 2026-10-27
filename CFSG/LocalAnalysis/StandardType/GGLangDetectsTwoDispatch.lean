module

public import CFSG.LocalAnalysis.StandardType.GGLangDetects
import CFSG.LieType.Chevalley.OddRootPairPermutation
import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoE
import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoF4
import CFSG.LocalAnalysis.StandardType.GGJ4dDetectTwoOuter
import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoPair
import CFSG.LocalAnalysis.StandardType.GGLangLatSolv

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem j4fNotSolv {C : Type*} [Group C] (hQ : CFSG.IsQuasisimple C) :
    ¬ Group.IsSolvable C := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  haveI : IsSimpleGroup (C ⧸ Subgroup.center C) := hsimple
  have : Nontrivial C := (QuotientGroup.mk_surjective (s := Subgroup.center C)).nontrivial
  exact Group.IsPerfect.not_isSolvable C

theorem langRatCentralizerDetectsPTwo_holds :
    LangRatCentralizerDetectsPTwo := by
  classical
  intro τ L _ _ p₀ p S hτ hp hp2 hpL hq π hπ ε hε hρ hpε hAlg a b ha hb hap hbp i hqs hle
  have hε1 : ε = -1 := by
    rcases hε with h | h
    · exfalso
      have h1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
        have := hpε
        rw [h, hq] at this
        simpa using this
      exact hp.one_lt.ne' (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h1))
    · exact h
  have hp3 : p = 3 := by
    have h1 : (p : ℤ) ∣ ((3 : ℕ) : ℤ) := by
      have := hpε
      rw [hε1, hq] at this
      simpa using this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (Int.natCast_dvd_natCast.1 h1)
  subst hp3
  have hq1 : S.D.q = 2 ^ 1 := by rw [hq]; norm_num
  have hnot : ¬ LangSmallSolv S.D.q S.ρ (rootCharHom a) i := by
    intro hs
    exact j4fNotSolv hqs
      (isSolvable_rationalComponent_of_latSolv S hq1 hp hpL π ε hε hpε hρ ha hap i
        (latSolv_of_langSmallSolv S hq1 hp hpL π ε hε hpε hρ ha hap i hs))
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S ha i
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  by_cases hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1
  · by_cases hF4 : τ = Tag.F4
    · subst hF4
      have hπ1 : π = 1 :=
        CFSG.LieType.Chevalley.perm_eq_one_of_cartanF4_parity π fun j k => by rw [hπ j k]
      have hρ' : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = -γ := by
        intro γ hγ
        have hl : latPerm (1 : Equiv.Perm (Fin Tag.F4.rank)) γ = γ := by
          funext k
          rfl
        rw [hρ γ hγ, hε1, hπ1, hl, neg_one_smul]
      exact langRatCentralizerDetects_two_F4 S hq hρ' ha hap hAlg i hnot hle
    · have hτE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        rcases hτ with h | h | h | h
        · exact absurd h hF4
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · have hrk : 2 < (componentRoots (rootCharHom a) i).ncard := by
          obtain ⟨x, hx⟩ : ∃ x, x ∈ componentRoots (rootCharHom a) i := by
            obtain ⟨a', ha'⟩ := Quotient.exists_rep i
            exact ⟨a'.1, a'.2, ha'⟩
          have hxr : IsRoot τ x := hΨ.isRoot x hx
          have hnx : -x ∈ componentRoots (rootCharHom a) i := hΨ.neg_mem x hx
          have hxne : x ≠ -x := by
            intro h
            apply hxr.ne_zero
            funext k
            have hk := congrFun h k
            simp only [Pi.neg_apply] at hk
            simp only [Pi.zero_apply]
            omega
          have h2 : 2 ≤ (componentRoots (rootCharHom a) i).ncard := by
            have hsub : ({x, -x} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots (rootCharHom a) i := by
              intro y hy
              rcases hy with rfl | rfl
              · exact hx
              · exact hnx
            have := Set.ncard_le_ncard hsub hfin
            rwa [Set.ncard_pair hxne] at this
          have hne2 : (componentRoots (rootCharHom a) i).ncard ≠ 2 := fun h =>
            hnot (Or.inl ⟨by rw [hs1, pow_one, hq]; norm_num, h⟩)
          omega
        exact langRatCentralizerDetects_two_inner_E S hτE hq ha hb i hinner hs1 hrk hle
      · exact langRatCentralizerDetects_two_outer S hτE hq π hπ hε1 hρ ha hb hap hAlg i hs1 hinner
          hnot hle
  ·
    have hne : rationalRoots S.ρ (rootCharHom a) i ≠ componentRoots (rootCharHom a) i := by
      intro hEq
      apply hs1
      have hmaps : ∀ γ ∈ componentRoots (rootCharHom a) i,
          S.ρ γ ∈ componentRoots (rootCharHom a) i := by
        intro γ hγ
        have h1 : S.ρ γ ∈ rationalRoots S.ρ (rootCharHom a) i := ⟨1, γ, hγ, rfl⟩
        rwa [hEq] at h1
      have himg : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i =
          componentRoots (rootCharHom a) i := by
        rw [Function.iterate_one]
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
        · rintro _ ⟨γ, hγ, rfl⟩
          exact hmaps γ hγ
        · exact (Set.ncard_image_of_injective _ S.ρ.injective).ge
      by_contra hne
      exact hmin 1 one_pos (by omega) himg
    exact langRatCentralizerDetects_two_pair S hτ hq π hπ hε hρ ha hb hAlg i hne hle

theorem langRatCentralizerDetectsP_holds :
    LangRatCentralizerDetectsP :=
  langRatCentralizerDetectsP_of_big_two langRatCentralizerDetectsPBig
    langRatCentralizerDetectsPTwo_holds

end CFSG.StandardType.LangRat

end
