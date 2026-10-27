module

public import CFSG.Quasithin.EmptyFaithful.SBd17I
public import CFSG.Quasithin.EmptyFaithful.SBd17CV
public import CFSG.Quasithin.EmptyFaithful.SBd16B2

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.not_mem_L_of_regular (r : RestHyp T Mc M V₁ V₂ Yp I L t) {X : Subgroup G}
    (hXY : X ≤ Yp) (hX3 : IsPGroup 3 ↥X)
    (hreg : Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) = ⊥) {σ : G}
    (hσS : σ ∈ Sgp153 T V₁) (hσN : σ ∈ Subgroup.normalizer (X : Set G)) (hσ1 : σ ≠ 1) : σ ∉ L := by
  intro hσL
  have hσQ : σ ∈ Sgp153 T V₁ ⊓ L := ⟨hσS, hσL⟩
  have hQ2 : IsPGroup 2 ↥(Sgp153 T V₁ ⊓ L) := r.sylow.2.1
  have hcomm : ∀ x ∈ X, σ * x = x * σ := by
    intro x hx
    have h1 : σ * x * σ⁻¹ * x⁻¹ ∈ X :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hσN x).mp hx) (Subgroup.inv_mem _ hx)
    have h2 : σ * x * σ⁻¹ * x⁻¹ ∈ Sgp153 T V₁ ⊓ L := by
      have hx' : x * σ⁻¹ * x⁻¹ ∈ Sgp153 T V₁ ⊓ L :=
        (Subgroup.mem_normalizer_iff.mp (r.Yp_le_Q (hXY hx)) σ⁻¹).mp (Subgroup.inv_mem _ hσQ)
      have : σ * x * σ⁻¹ * x⁻¹ = σ * (x * σ⁻¹ * x⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hσQ hx'
    have h3 : σ * x * σ⁻¹ * x⁻¹ = 1 :=
      SylowX.eq_one_of_isPGroup_two_three hQ2 hX3 h2 h1
    calc σ * x = (σ * x * σ⁻¹ * x⁻¹) * (x * σ) := by group
      _ = x * σ := by rw [h3, one_mul]
  have : σ ∈ Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) :=
    ⟨hσQ, Subgroup.mem_centralizer_iff.mpr fun x hx => (hcomm x hx).symm⟩
  rw [hreg, Subgroup.mem_bot] at this
  exact hσ1 this

theorem RestHyp.centralizer_V₁_eq (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hK1 : ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I) {τ σ : G}
    (hτS : τ ∈ Sgp153 T V₁) (hτ2 : τ * τ = 1) (hτm : ∃ v ∈ V₁, τ * v ≠ v * τ)
    (hσS : σ ∈ Sgp153 T V₁) (hσc : ∀ v ∈ V₁, σ * v = v * σ) (hσL : σ ∉ L) :
    Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers σ := by
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V₁, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h4 := r.ctx.hyp.decomp.card₁
    rw [this, Subgroup.card_bot] at h4
    omega
  have hle : Subgroup.centralizer (V₁ : Set G) ≤ I :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)).trans (hK1 v hv hv1)
  rw [← r.centralizer_I_V₁ h113 (r.relIndex_L_I h113) hτS hτ2 hτm hσS hσc hσL]
  exact (inf_eq_right.mpr hle).symm

end CFSG.Quasithin.SBd14

