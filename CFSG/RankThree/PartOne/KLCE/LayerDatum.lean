module

public import CFSG.RankThree.PartOne.KLCE.TypeSL
public import CFSG.RankThree.PartOne.KLCE.EngineGroup

public section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

@[expose] def LayerDatum (p : ℕ) {M : Type} [Group M] (F₀ : M → M) (P : Subgroup M) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ψ : G →* M), Function.Injective ψ → P ≤ ψ.range →
    ∀ α : MulAut G, α ^ p = 1 → (∀ g, ψ (α g) = F₀ (ψ g)) → ∀ x : G, orderOf x = p →
    CFSG.pRank p G = 1 → (∀ y ∈ P.comap ψ, y * x = x * y) →
    (∀ g ∈ P.comap ψ, α g ∈ P.comap ψ) →
    (∀ e ∈ P.comap ψ, ¬ ∀ g ∈ P.comap ψ, α g = e * g * e⁻¹) ∧
    (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥(P.comap ψ) ⧸ Subgroup.center ↥(P.comap ψ)) t' n' 2 (p * f')) ∧
    ∃ t₁ ∈ P.comap ψ, α t₁ = t₁ ∧ ∃ t₂ ∈ P.comap ψ, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

theorem layerDatum_of_sl {p f' m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmp : m + 2 < p)
    (hf' : 1 ≤ f') {M : Type} [Group M] (F₀ : M → M) (P : Subgroup M) {K' : Type} [Field K']
    [Finite K'] [CharP K' 2] (hK' : Nat.card K' = 2 ^ (p * f')) {σ' : K' ≃+* K'} (hσ' : σ' ≠ 1)
    (ρ' : SpecialLinearGroup (Fin (m + 2)) K' →* M) (hρ' : Function.Injective ρ')
    (hrange : ρ'.range = P)
    (hF : ∀ d, F₀ (ρ' d) = ρ' (SpecialLinearGroup.map σ'.toRingHom d)) :
    LayerDatum p F₀ P := by
  intro G _ _ ψ hψ hPψ α hα hψα x hx hpr hcent hstab
  have hρψ : ρ'.range ≤ ψ.range := hrange ▸ hPψ
  obtain ⟨φ, hφinj, hψφ, hφrange⟩ := exists_hom_of_push ψ hψ ρ' hρ' hρψ
  have hQ : φ.range = P.comap ψ := by rw [hφrange, hrange]
  have hαφ : ∀ B, α (φ B) = φ (SpecialLinearGroup.map σ'.toRingHom B) := fun B => by
    apply hψ
    rw [hψα, hψφ, hF, hψφ]
  obtain ⟨-, hmove, hZ, hmodel, hfix⟩ := sl_type_claims hp5 hf' hK' hσ' α φ hφinj hαφ _ hQ
  refine ⟨?_, hmodel, hfix⟩
  have hstab' : ∀ g ∈ P.comap ψ, α g ∈ P.comap ψ := hstab
  exact component_outer hp hpr hx hα hcent hstab' (n := m + 2) (by omega) hmp hZ hmove

end CFSG.RankThree.PartOne.KLCE
