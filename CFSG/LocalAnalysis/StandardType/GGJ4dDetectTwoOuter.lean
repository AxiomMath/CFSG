module

public import CFSG.LocalAnalysis.StandardType.GGJ4dMixed
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d

theorem langRatCentralizerDetects_two_outer
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (π : Equiv.Perm (Fin τ.rank)) (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {ε : ℤ} (hε : ε = -1) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {a b : Fin τ.rank → Lˣ} (ha : rootDiagUnit τ a ∈ S.D.torus)
    (hb : rootDiagUnit τ b ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1) (hAlg : S.IsAlgebraic)
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hnot : ¬ LangSmallSolv S.D.q S.ρ (rootCharHom a) i)
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer {rootDiagUnit τ b}) :
    ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1 := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have himg : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ :=
    j4d_image_eq_of_componentOrbitLength_eq_one hs1
  have hstab : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
    rw [← himg]
    exact ⟨γ, hγ, rfl⟩
  have hrr : rationalRoots S.ρ (rootCharHom a) i = Ψ :=
    j4d_rationalRoots_eq_componentRoots S i hstab
  intro γ hγ
  have hγΨ : γ ∈ Ψ := by rwa [hrr] at hγ
  by_cases hstable : ∀ δ ∈ Ψ, S.ρ δ = δ ∨ S.ρ δ = -δ
  ·
    have hout1 : ¬ twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[1]) := by
      have h := hout
      rw [hs1] at h
      rwa [hΨdef]
    exact j4d_allStable_kills S hτ hq hAlg i hstable hnot hout1 hle γ hγΨ
  ·
    have hmixed := hstable
    push Not at hmixed
    obtain ⟨δ, hδΨ, hδ1, hδ2⟩ := hmixed
    have hτE6 : τ = .E6 := by
      rcases hτ with h | h | h
      · exact h
      · exfalso
        subst h
        have hπ1 : π = 1 := perm_eq_one_of_cartan_E7 π (by simpa using hπ)
        apply hstable
        intro x hx
        have hxr : IsRoot Tag.E7 x := isRoot_of_mem_componentRoots hx
        exact Or.inr (by
          rw [hρ x hxr, hε, hπ1, neg_one_smul]
          rfl)
      · exfalso
        subst h
        have hπ1 : π = 1 := perm_eq_one_of_cartan_E8 π (by simpa using hπ)
        apply hstable
        intro x hx
        have hxr : IsRoot Tag.E8 x := isRoot_of_mem_componentRoots hx
        exact Or.inr (by
          rw [hρ x hxr, hε, hπ1, neg_one_smul]
          rfl)
    subst hτE6
    have hπeq : π = e6Graph := by
      rcases perm_eq_one_or_eq_sigma_of_cartan_E6 π hπ with h | h
      · exfalso
        apply hstable
        intro x hx
        have hxr : IsRoot Tag.E6 x := isRoot_of_mem_componentRoots hx
        exact Or.inr (by
          rw [hρ x hxr, hε, h, neg_one_smul]
          rfl)
      · rw [h]
        rfl
    have hρ' : ∀ x, IsRoot Tag.E6 x → S.ρ x = -latPerm e6Graph x := by
      intro x hx
      rw [hρ x hx, hε, hπeq, neg_one_smul]
    have hnoanti : ∀ x, IsRoot Tag.E6 x → latPerm e6Graph x ≠ -x :=
      fun x hx => j4dE6Sigma_no_antifixed hx
    have hmoved : ∃ δ ∈ componentRoots (rootCharHom a) i, S.ρ δ ≠ -δ :=
      ⟨δ, hδΨ, hδ2⟩
    exact j4d_mixed_detects S hq hAlg i e6Graph_cartan hρ' hnoanti hstab hmoved hle γ hγΨ

end CFSG.StandardType.LangRat

end
