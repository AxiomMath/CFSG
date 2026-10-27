module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

@[expose] def RCKF4Envelope
    : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (S : LangSetup Tag.F4 GGL 5) (a : Fin Tag.F4.rank → GGLˣ),
      rootDiagUnit Tag.F4 a ∈ S.D.torus → rootDiagUnit Tag.F4 a ≠ 1 → (∀ j, a j ^ p = 1) →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RCKNonclassShape S.ρ (componentRoots (rootCharHom a) i) ∨
          RCKClassicalShape S.D.q S.ρ (rootCharHom a) i ∨
          RCKSmallShape S.D.q S.ρ (rootCharHom a) i

@[expose] def RCKNoSmallSU3
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL))
      (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)),
      RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i →
      ¬ (twistKind S.ρ (rootCharHom a) i = .suN ∧
          compRank (componentRoots (rootCharHom a) i) = 2)

@[expose] def RCKNoSmallB2
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL))
      (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)),
      RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i →
      ¬ (langTag t = Tag.F4 ∧ compRank (componentRoots (rootCharHom a) i) = 2 ∧
          (componentRoots (rootCharHom a) i).ncard = 8 ∧
          S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4)

theorem rckNoSmall_of_cases
    (h1 : RCKNoSmallSU3) (h2 : RCKNoSmallB2) : RCKNoSmall := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp hsmall
  rcases hsmall with h | h
  · exact h1 X t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp h
  · exact h2 X t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp h

theorem rckNC_exc_shape {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ} {i : KernelComponent χ}
    (h : twistKind ρ χ i = .exc) : RCKNonclassShape ρ (componentRoots χ i) := by
  unfold twistKind at h
  split_ifs at h with c1 c2 c3 c4 <;>
    first
    | exact absurd h (by decide)
    | (rcases c2 with c2 | c2
       · exact Or.inl c2
       · exact Or.inr (Or.inr c2))

theorem rckNC_envelope_of_ade
    {τ : Tag} (hτ : τ = Tag.E6 ∨ τ = Tag.E7 ∨ τ = Tag.E8)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (q : ℕ) (a : Fin τ.rank → GGLˣ)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hshape : RCKADEShape ρ (rootCharHom a) i) :
    RCKNonclassShape ρ (componentRoots (rootCharHom a) i) ∨
      RCKClassicalShape q ρ (rootCharHom a) i ∨ RCKSmallShape q ρ (rootCharHom a) i := by
  rcases hshape with h | h | h | h | h | h | h
  · exact Or.inr (Or.inl (by unfold RCKClassicalShape; tauto))
  · exact Or.inr (Or.inl (by unfold RCKClassicalShape; tauto))
  · exact Or.inr (Or.inl (by unfold RCKClassicalShape; tauto))
  · exact Or.inr (Or.inl (by unfold RCKClassicalShape; tauto))
  · exact Or.inr (Or.inl (by unfold RCKClassicalShape; tauto))
  · obtain ⟨-, hE⟩ := h
    rcases hE with ⟨hr, hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
    · exact Or.inl (Or.inl ⟨hr, hc⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨hr, hc⟩))
    · exfalso
      have hsub : componentRoots (rootCharHom a) i ⊆ {γ : Fin τ.rank → ℤ | IsRoot τ γ} :=
        fun γ hγ => hγ.1.1
      have hfin : {γ : Fin τ.rank → ℤ | IsRoot τ γ}.Finite := finite_setOf_isRoot τ
      have hset : {γ : Fin τ.rank → ℤ | IsRoot τ γ} = ↑(rootFinset τ) :=
        Set.ext fun γ => by simp [mem_rootFinset]
      have hcard : {γ : Fin τ.rank → ℤ | IsRoot τ γ}.ncard = τ.rootCount := by
        rw [hset, Set.ncard_coe_finset, card_rootFinset]
      have hle := Set.ncard_le_ncard hsub hfin
      rw [hcard, hc] at hle
      have hE8 : τ = Tag.E8 := by
        rcases hτ with rfl | rfl | rfl
        · exact absurd hle (by decide)
        · exact absurd hle (by decide)
        · rfl
      subst hE8
      have heq : componentRoots (rootCharHom a) i = {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ} :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [hc, hcard]; rfl) hfin
      apply ha1
      have h1 : a = 1 := by
        funext j
        have hj : (Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
          rw [heq]
          exact isRoot_single Tag.E8 j
        have h2 := hj.1.2
        have h3 := rootChar_nsmul_single a j 1
        rw [one_smul, pow_one] at h3
        exact (h3.symm.trans h2)
      rw [h1]
      exact map_one (rootDiagUnitHom Tag.E8 GGL)
  · exact Or.inl (rckNC_exc_shape h)

theorem rckClassEnvelope_tag
    (hADE : RCKStdEnvelope) (hF4 : RCKF4Envelope) (τ : Tag)
    (hτ : τ = Tag.F4 ∨ τ = Tag.E6 ∨ τ = Tag.E7 ∨ τ = Tag.E8) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ)
    (haT : rootDiagUnit τ a ∈ S.D.torus) (ha1 : rootDiagUnit τ a ≠ 1) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RCKNonclassShape S.ρ (componentRoots (rootCharHom a) i) ∨
      RCKClassicalShape S.D.q S.ρ (rootCharHom a) i ∨
      RCKSmallShape S.D.q S.ρ (rootCharHom a) i := by
  rcases hτ with rfl | hτ | hτ | hτ
  · exact hF4 p hp hp2 S a haT ha1 hap i hqs
  all_goals
    have hsh := hADE τ (by tauto) S p hp hp2 a haT ha1 hap i hqs
    exact rckNC_envelope_of_ade (by tauto) S.ρ S.D.q a ha1 i hsh

theorem rckClassEnvelope_of_pieces
    (hADE : RCKStdEnvelope) (hF4 : RCKF4Envelope) : RCKClassEnvelope :=
  fun t _ p hp hp2 S a haT ha1 hap i hqs =>
    rckClassEnvelope_tag hADE hF4 (langTag t) (langTag_five t) p hp hp2 S a haT ha1 hap i hqs

end CFSG.StandardType.RCKRP
