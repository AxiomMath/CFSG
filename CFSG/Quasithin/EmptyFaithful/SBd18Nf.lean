module

public import CFSG.Quasithin.EmptyFaithful.SBd18Cl

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.not_conj_V₁_of_swap (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    (hI : I = Subgroup.normalizer (V₁ : Set G))
    (hK1 : ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I)
    (hTI : ∀ (g x : G), x ∈ V₁ → x ≠ 1 → g⁻¹ * x * g ∈ V₁ → g ∈ Subgroup.normalizer (V₁ : Set G))
    {τ f t₀ : G} (hτS : τ ∈ Sgp153 T V₁) (hfS : f ∈ Sgp153 T V₁) (hττ : τ * τ = 1)
    (hff : f * f = 1) (hτf : τ * f = f * τ) (hcent : ∀ v ∈ V₁, (τ * f) * v = v * (τ * f))
    (hmove : ∃ v ∈ V₁, τ * v ≠ v * τ) (hσL : τ * f ∉ L)
    (hcl : Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers (τ * f))
    (ht₀ : t₀ * τ * t₀⁻¹ = τ * f) :
    ∀ g : G, g⁻¹ * τ * g ∉ V₁ := by
  classical
  have D0 := r.ctx.hyp.decomp
  have hσS : τ * f ∈ Sgp153 T V₁ := Subgroup.mul_mem _ hτS hfS
  have hσ2 : (τ * f) * (τ * f) = 1 := by
    calc τ * f * (τ * f) = τ * (f * τ) * f := by group
      _ = τ * (τ * f) * f := by rw [← hτf]
      _ = (τ * τ) * (f * f) := by group
      _ = 1 := by rw [hττ, hff, one_mul]
  have hσI : τ * f ∈ I := r.S_le_I hσS
  obtain ⟨F, hFL, hF3, -, hFσ, hFC⟩ := r.exists_sigma_data h113 hOut hτS hττ hmove hσS hσ2 hcent hσL
  have hnot := SBd18.not_conj_into_V₁ (V₁ := V₁) (L := L) (F := F) (σ := τ * f) D0.card₁
    (fun v hv => r.V_sq v (D0.le₁ hv)) (r.V₁_le_L h113)
    (fun l hl v hv => Subgroup.mem_centralizer_iff.mp (r.h1 hv) l hl) hσ2 hσL hcent
    (r.hNL hσI) hcl (fun v hv hv1 => hI ▸ hK1 v hv hv1) hTI hFL hF3 hFσ hFC
  intro g hg
  apply hnot (t₀ * g)
  have e : (t₀ * g)⁻¹ * (τ * f) * (t₀ * g) = g⁻¹ * τ * g := by
    rw [← ht₀]
    group
  rw [e]
  exact hg

end CFSG.Quasithin.SBd14
