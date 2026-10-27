module

public import CFSG.Quasithin.EmptyFaithful.SBd18T0
public import CFSG.Quasithin.EmptyFaithful.SBd16B1
public import CFSG.Quasithin.EmptyFaithful.SBd16B2
public import CFSG.Quasithin.EmptyFaithful.SBd16Gen

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.exists_fusion_package_t0 (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    ∃ (X : Subgroup G) (τ f : G), X ≤ Yp ∧ IsPGroup 3 ↥X ∧ ¬ 3 ∣ X.relIndex Yp ∧
      Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      τ ∈ Sgp153 T V₁ ∧ f ∈ Sgp153 T V₁ ∧ τ ∈ Subgroup.normalizer (X : Set G) ∧
      f ∈ Subgroup.normalizer (X : Set G) ∧ τ * τ = 1 ∧ f * f = 1 ∧ τ * f = f * τ ∧ τ ≠ 1 ∧
      f ≠ 1 ∧ τ ≠ f ∧
      (∀ s ∈ Sgp153 T V₁ ⊓ Subgroup.normalizer (X : Set G), s = 1 ∨ s = τ ∨ s = f ∨ s = τ * f) ∧
      (∀ x ∈ X, f * x * f⁻¹ = x⁻¹) ∧ (∀ v ∈ V₁, (τ * f) * v = v * (τ * f)) ∧
      (∃ v ∈ V₁, τ * v ≠ v * τ) ∧
      (∃ t₀ ∈ T ⊓ Subgroup.normalizer (X : Set G),
        t₀ * τ * t₀⁻¹ = τ * f ∧ t₀ * (τ * f) * t₀⁻¹ = τ) ∧
      ∃ g : G, g⁻¹ * τ * g ∈ Sgp153 T V₁ ⊓ L ∨ f⁻¹ * (g⁻¹ * τ * g) ∈ Sgp153 T V₁ ⊓ L := by
  classical
  obtain ⟨X, hXY, hX3, hXidx, hXV, hreg, hfrat⟩ := r.exists_sylow_X h113
  have hRQ := r.R_eq_Q h113
  obtain ⟨τ, f, hτS, hfS, hτN, hfN, hττ, hff, hτf, hτ1, hf1, hτf', hcl, hinv, hcent, hmove,
    ⟨W, hWT, hWi, hτW, hWinv⟩, t₀, ht₀N, ht₀τ, ht₀f, -, -⟩ :=
    r.exists_fusion_elements_t0 hXY hX3 hXV hRQ hreg hfrat
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have hq := hyp.qtfe
  have hG := SBd16.no_index_two_of_simple hq.simple hq.nonabelian
  obtain ⟨g, hg⟩ := SBd16.exists_conj_mem_of_index_two hG hq.sylow.1 hq.sylow.2 hWT hWi hτS.1 hτW
    hττ
  refine ⟨X, τ, f, hXY, hX3, hXidx, hreg, hτS, hfS, hτN, hfN, hττ, hff, hτf, hτ1, hf1, hτf', hcl,
    hinv, hcent, hmove, ⟨t₀, ht₀N, ht₀τ, ht₀f⟩, g, ?_⟩
  refine hWinv _ hg ?_
  calc g⁻¹ * τ * g * (g⁻¹ * τ * g) = g⁻¹ * (τ * τ) * g := by group
    _ = 1 := by rw [hττ]; group

end CFSG.Quasithin.SBd14
