module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMOmegaSmall
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMOmegaLarge
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMOmegaFourMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMOmegaFourPlus
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag StatedOmega)


private theorem exists_mulEquiv_statedOmega_of_big {f : ℕ} (hf : 1 ≤ f) {ι₁ : Type} [Fintype ι₁]
    [DecidableEq ι₁] (Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f))
    (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (hbig : 6 ≤ Fintype.card ι₁ ∨ (Fintype.card ι₁ = 4 ∧
      ¬ ∃ S : Submodule (GaloisField 2 f) (ι₁ → GaloisField 2 f),
        Module.finrank (GaloisField 2 f) S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0)) :
    ∃ (t : StatedLieTag) (m g : ℕ), RCKClassicalTag t ∧ 1 ≤ g ∧
      Nonempty ((ggU t m g).K ≃* ↥(StatedOmega ⇑Φ₁)) := by
  rcases hbig with h6 | ⟨h4, hminus⟩
  · obtain ⟨t, m, htag, hΘ⟩ := exists_mulEquiv_statedOmega_of_six_le hf Φ₁ hΦ₁ h6
    exact ⟨t, m, f, htag, hf, hΘ⟩
  · obtain ⟨hΘ⟩ := nonempty_mulEquiv_statedOmega_four_minus hf Φ₁ hΦ₁ h4 hminus
    exact ⟨.PSL, 2, 2 * f, Or.inl rfl, by omega, ⟨hΘ⟩⟩

theorem rckBlockModel_omegaFixed {W : Type} [Group W] {H : Subgroup W} {C : Subgroup ↥H}
    (hCo : CFSG.Open.IsComponentOf C ⊤) {f : ℕ} (hf : 1 ≤ f) {ι₁ : Type} [Fintype ι₁]
    [DecidableEq ι₁] (Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f))
    (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (hsmall : ¬ (Nat.card (GaloisField 2 f) = 2 ∧ Fintype.card ι₁ = 4 ∧
      ∃ S : Submodule (GaloisField 2 f) (ι₁ → GaloisField 2 f),
        Module.finrank (GaloisField 2 f) S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0))
    (Ψ : ↥H ≃* ↥(StatedOmega ⇑Φ₁)) :
    ∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →* ↥H),
      RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m g κ := by
  have hmap : CFSG.Open.IsComponentOf (C.map Ψ.toMonoidHom) ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv Ψ hCo
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr Ψ.surjective] at h
  have hcard_even : Even (Fintype.card ι₁) := by
    obtain ⟨n, hn⟩ :=
      (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        Φ₁ hΦ₁).1
    rw [Module.finrank_fintype_fun_eq_card] at hn
    exact ⟨n, by omega⟩
  by_cases h2 : Fintype.card ι₁ ≤ 2
  · exfalso
    exact (not_isComponentOf_statedOmega_of_card_le_two (K := GaloisField 2 f) Φ₁ hΦ₁ h2 _)
      hmap
  · by_cases hplus4 : Fintype.card ι₁ = 4 ∧
        ∃ S : Submodule (GaloisField 2 f) (ι₁ → GaloisField 2 f),
          Module.finrank (GaloisField 2 f) S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0
    · obtain ⟨h4, hplus⟩ := hplus4
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have hcard : Nat.card (GaloisField 2 f) = 2 := by
          rw [GaloisField.card 2 f (by omega)]
          have hf1 : f = 1 := by omega
          rw [hf1]
          norm_num
        exact hsmall ⟨hcard, h4, hplus⟩
      obtain ⟨κ, hκ⟩ := rckBlockModel_omegaFourPlus hCo hf2 Φ₁ hΦ₁ h4 hplus Ψ
      exact ⟨.PSL, 2, f, κ, Or.inl rfl, hf, hκ⟩
    · have hbig : 6 ≤ Fintype.card ι₁ ∨ (Fintype.card ι₁ = 4 ∧
          ¬ ∃ S : Submodule (GaloisField 2 f) (ι₁ → GaloisField 2 f),
            Module.finrank (GaloisField 2 f) S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0) := by
        by_cases h4 : Fintype.card ι₁ = 4
        · exact Or.inr ⟨h4, fun hS => hplus4 ⟨h4, hS⟩⟩
        · left
          obtain ⟨n, hn⟩ := hcard_even
          omega
      have hA : CFSG.Assembly.IsComponentOf (C.map Ψ.toMonoidHom) ⊤ :=
        (CFSG.Assembly.isComponentOf_iff_open).2 hmap
      have hQ : CFSG.Assembly.IsQuasisimple ↥(StatedOmega ⇑Φ₁) :=
        isQuasisimple_statedOmega Φ₁ hΦ₁ hbig
      have htop : C.map Ψ.toMonoidHom = ⊤ :=
        CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple
          ((CFSG.Assembly.IsQuasisimple.congr Subgroup.topEquiv).mpr hQ) hA
      have hCtop : C = ⊤ := by
        refine le_antisymm le_top ?_
        intro x _
        have hx : Ψ x ∈ C.map Ψ.toMonoidHom := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
        rw [← Ψ.injective hcx]
        exact hc
      obtain ⟨t, m, g, htag, hg, Θ⟩ :=
        exists_mulEquiv_statedOmega_of_big hf Φ₁ hΦ₁ hbig
      obtain ⟨Θ⟩ := Θ
      refine ⟨t, m, g, (Θ.trans Ψ.symm).toMonoidHom, htag, hg, ?_⟩
      rw [hCtop]
      exact rckModelConverse_top (Θ.trans Ψ.symm).injective (Θ.trans Ψ.symm).surjective

end CFSG.StandardType.RCKRP
