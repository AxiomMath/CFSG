module

public import CFSG.LocalAnalysis.StandardType.GGLangTwoPairAux

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem langRatCentralizerDetects_two_pair
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (π : Equiv.Perm (Fin τ.rank)) (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {a b : Fin τ.rank → Lˣ} (ha : rootDiagUnit τ a ∈ S.D.torus)
    (hb : rootDiagUnit τ b ∈ S.D.torus) (hAlg : S.IsAlgebraic) (i : KernelComponent (rootCharHom a))
    (hne : rationalRoots S.ρ (rootCharHom a) i ≠ componentRoots (rootCharHom a) i)
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Subgroup.centralizer {rootDiagUnit τ b}) :
    ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1 := by
  classical
  have hρρ : ∀ γ, IsRoot τ γ → S.ρ (S.ρ γ) = γ := fun γ hγ =>
    rho_rho_eq_of_latPerm S hτ π hπ hε hρ hγ
  rcases langOrbit_cases_of_rho_rho S hρρ ha i with
    ⟨_, hunion1⟩ | ⟨_, j, hji, himg, hunion, horth⟩
  · exact absurd hunion1 hne
  · have key : ∀ γ ∈ componentRoots (rootCharHom a) i,
        rootChar b γ = 1 ∧ rootChar b (S.ρ γ) = 1 := by
      intro γ hγ
      have hβcomp : S.ρ γ ∈ componentRoots (rootCharHom a) j := by
        rw [← himg]
        exact ⟨γ, hγ, rfl⟩
      have hρβ : S.ρ (S.ρ γ) = γ := hρρ γ hγ.1.1
      have horth0 : iform γ (S.ρ γ) = 0 := horth γ hγ (S.ρ γ) hβcomp
      exact j4e_pair_detects S hτ hq hAlg i hji hle hγ hβcomp rfl hρβ horth0
    have hρj : ∀ δ ∈ componentRoots (rootCharHom a) j,
        S.ρ δ ∈ componentRoots (rootCharHom a) i := by
      intro δ hδ
      rw [← himg] at hδ
      obtain ⟨α, hα, rfl⟩ := hδ
      rw [hρρ α hα.1.1]
      exact hα
    intro γ' hγ'
    rw [hunion] at hγ'
    rcases hγ' with h | h
    · exact (key γ' h).1
    · have hρback := hρj γ' h
      have hres := (key (S.ρ γ') hρback).2
      rwa [hρρ γ' h.1.1] at hres

end CFSG.StandardType.LangRat

end
