module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTriD4D4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore

theorem tag_of_twistKind_exc_of_compRank_four
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    (hap : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4) :
    τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
  have h24 : (componentRoots (rootCharHom a) i).ncard = 24 := by
    unfold twistKind at hk
    split_ifs at hk with h1 h2 <;> try cases hk
    rcases h2 with ⟨h6, -⟩ | ⟨-, h24, -⟩
    · omega
    · exact h24
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [h4] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL
      CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_F4 hap
    obtain ⟨x, C, -, -, -, hr, hc⟩ := hpinned i
    exact absurd (hc ▸ h24) (kacCount_F4_four C (hr ▸ h4))
  | D4 => exact Or.inl rfl
  | E6 => exact Or.inr (Or.inl rfl)
  | E7 => exact Or.inr (Or.inr (Or.inl rfl))
  | E8 => exact Or.inr (Or.inr (Or.inr rfl))

@[expose] def RCKRetTriD4E
    : Prop :=
  ∀ (τ : Tag), (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ), S.D.q = 2 ^ h →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
    RCKReturnedCover S a i h
      (fun M g =>
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
          TriField F σ g ∧ M = triD4Universal F σ)


theorem rckRetTriD4_of_pair_of_E (hP : RCKPairTriD4) (hE : RCKRetTriD4E) : RCKRetTriD4 := by
  intro τ S a haT p hp hp2 hap i h hq hqs hshape
  have hpL : (p : GGL) ≠ 0 := fun h0 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    ((CharP.cast_eq_zero_iff GGL 2 p).mp h0)).symm
  rcases tag_of_twistKind_exc_of_compRank_four S hp hpL hap i
      (twistKind_eq_exc_of_triD4Shape S i hshape.1 hshape.2.1 hshape.2.2) hshape.1 with
    rfl | rfl | rfl | rfl
  · exact rckRetTriD4_D4_of_pair hP S a haT p hp hp2 hap i h hq hqs hshape
  · exact hE .E6 (Or.inl rfl) S a haT p hp hp2 hap i h hq hqs hshape
  · exact hE .E7 (Or.inr (Or.inl rfl)) S a haT p hp hp2 hap i h hq hqs hshape
  · exact hE .E8 (Or.inr (Or.inr rfl)) S a haT p hp hp2 hap i h hq hqs hshape

end CFSG.StandardType.RCKRP

end
