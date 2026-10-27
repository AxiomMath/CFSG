module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2F4Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2F4NC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLPos
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PosGlue

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.LieKnownR2.F4

@[expose] def GGSixF4PosExplicit :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .F4 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x →
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .F4 n f p ψ R Rm ∧ 1 ≤ f ∧
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
        CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
        Odd (Nat.card (Subgroup.center ↥K)) →
        (∃ (m : ℕ) (β : Fin (ggU .PSp m f).D.rank → ℤ), (m = 2 ∨ m = 3) ∧ ¬ (m = 2 ∧ f = 1) ∧
            β ∈ (ggU .PSp m f).D.roots ∧ GGRootVia (ggU .PSp m f) K R β) ∨
          (∃ β : Fin (ggU .PSL 3 f).D.rank → ℤ, 3 ≤ f ∧ β ∈ (ggU .PSL 3 f).D.roots ∧
            GGRootVia (ggU .PSL 3 f) K R β) ∨
          (∃ β : Fin (ggU .PSU 3 f).D.rank → ℤ, 2 ≤ f ∧ β ∈ (ggU .PSU 3 f).D.roots ∧
            GGLongRoot (ggU .PSU 3 f).D β ∧ GGRootVia (ggU .PSU 3 f) K R β) ∨
          K = G₀

private theorem l10sf4p_pair_ne {m f : ℕ} (hmf : ¬ (m = 2 ∧ f = 1)) (hf : 1 ≤ f) :
    (m, 2 ^ f) ≠ (2, 2) := by
  intro hpair
  obtain ⟨hm2, hpow⟩ := Prod.mk.inj hpair
  have hf2 : 2 ≤ f := by omega
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  omega

theorem ggSixLieKnownPos_F4_of_explicit
    (hpos : GGSixF4PosExplicit) : GGSixLieKnownPos .F4 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hf, hcases⟩ := hpos X n f ψ p G₀ B₁ D J L x hH
  obtain ⟨β₀, hβ₀, -, u₀, hR₀, -⟩ := id hpos0
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, ?_, ?_⟩
  · intro e he hene K hKG hKcomp hJK hKne hKodd
    rcases hcases e he hene K hKG hKcomp hJK hKne hKodd with
      ⟨m, β, hm, hmf, hβ, φ, hφ, hker, u, hR⟩ | ⟨β, hf3, hβ, φ, hφ, hker, u, hR⟩ |
      ⟨β, hf2, hβ, hlong, φ, hφ, hker, u, hR⟩ | hKG₀
    · rw [← hφ, hR]
      exact ⟨PSp.ggRootInnerAt_ggU_psp (by omega) φ hker hβ u,
        PSp.ggRootNoCentralAt_ggU_psp ⟨Nat.prime_two, hf, by omega, l10sf4p_pair_ne hmf hf⟩
          φ hker hβ u⟩
    · rw [← hφ]
      exact PSL.itemTwo_ggU_psl (k := 2) (Or.inr (Or.inr ⟨hf3, le_rfl⟩)) φ hker hβ u hR
    · rw [← hφ, hR]
      exact ⟨PSU.ggRootInnerAt_ggU_psu le_rfl (by omega) φ hker hβ (Or.inl hlong) u,
        PSU.ggRootNoCentralAt_ggU_psu le_rfl (by omega) φ hker hβ (Or.inl hlong) u⟩
    · rw [hKG₀, ← h1, hR₀]
      exact ⟨ggRootInnerAt_ggU_f4 hf ψ h2 hβ₀ u₀, ggRootNoCentralAt_ggU_f4 ψ h2 hβ₀ u₀⟩
  · intro Y hY hYnorG hYnorR hcomm
    rw [← h1] at hYnorG hcomm ⊢
    exact itemThree_ggU_f4 hf ψ h2 hβ₀ u₀ hR₀ Y hY hYnorG hYnorR hcomm

end CFSG.StandardType.LieKnownR2.F4
