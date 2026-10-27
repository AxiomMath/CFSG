module

public import CFSG.Quasithin.H13.GoldschmidtU43CQ8

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

structure JWData {z t w a a' : G} (e : Two z t w a a') (R : Subgroup ↥(Hz z))
    (u u' σ₁ : ↥(Hz z)) (x : ↥(Uz z)) (n₁ : V4) : Prop where
  hu : u ∈ Subgroup.normalizer (R : Set ↥(Hz z))
  hu' : u' ∈ Subgroup.normalizer (R : Set ↥(Hz z))
  hu2 : u * u = 1
  hu'2 : u' * u' = 1
  hcomm : u * u' * u⁻¹ * u'⁻¹ = zK z
  hact : e.swap.hyp.act u = e.swap.hyp.act (e.swap.mK e.ha)
  hact' : e.swap.hyp.act u' = e.swap.hyp.act (e.swap.mK e.ha')
  hp : SwapPairA (e.swap.hyp.act u) (e.swap.hyp.act u')
  hσR : σ₁ ∈ R
  hρ1 : e.swap.hyp.act σ₁ ≠ 1
  hρfix : ∀ v, InP2 v → vapp (e.swap.hyp.act σ₁) v = v
  hn₁ : InP1 n₁
  hn₁0 : n₁ ≠ 0
  hcn₁ : vapp (e.swap.hyp.act u * e.swap.hyp.act u') n₁ = n₁
  hrefl : ∀ ξ, InP1 ξ → ξ ≠ 0 → ξ ≠ n₁ →
    vapp (e.swap.hyp.act u * e.swap.hyp.act u') ξ = ξ + n₁
  hx : e.swap.hyp.tv x = n₁
  hsign : conjU σ₁⁻¹ (conjU σ₁⁻¹ x) = x * conjU σ₁⁻¹ x

namespace Two

variable [Finite G] {z t w a a' : G} (e : Two z t w a a')
  {R : Subgroup ↥(Hz z)} (hR : SylR e.swap.hyp R)
include hR

theorem exists_data : ∃ (u u' σ₁ : ↥(Hz z)) (x : ↥(Uz z)) (n₁ : V4), JWData e R u u' σ₁ x n₁ := by
  have h := e.swap.hyp
  obtain ⟨u, u', hu, hu', hau, hau', hu2, hu'2, hcomm⟩ := e.exists_uu' hR
  have hs1 := e.swap.act_mK_ne_one e.ha
  have hs2 := e.swap.act_mK_ne_one e.ha'
  obtain ⟨hsw1, hss1, -⟩ := fix_swapA (e.swap.linePair_ta e.ha) (h.act_mem_Oq _)
    (e.swap.vapp_mK_tau e.ha) (e.swap.vapp_mK_alpha e.ha) hs1
  obtain ⟨hsw2, hss2, -⟩ := fix_swapA (e.swap.linePair_ta e.ha') (h.act_mem_Oq _)
    (e.swap.vapp_mK_tau e.ha') (e.swap.vapp_mK_alpha e.ha') hs2
  obtain ⟨hcm, hne⟩ := fix_pairA (e.swap.linePair_ta e.ha) (e.swap.linePair_ta e.ha')
    e.bq_eq_one (h.act_mem_Oq _) (h.act_mem_Oq _) (e.swap.vapp_mK_tau e.ha)
    (e.swap.vapp_mK_alpha e.ha) hs1 (e.swap.vapp_mK_tau e.ha') (e.swap.vapp_mK_alpha e.ha') hs2
  have hp : SwapPairA (h.act u) (h.act u') := by
    rw [hau, hau']
    exact ⟨hsw1, hsw2, hss1, hss2, hcm, hne⟩
  obtain ⟨ρ₁, hρR, hρne, hρfix⟩ := exists_rhoA
  obtain ⟨σ₁, hσR, hσρ⟩ := hR.act_onto hρR
  obtain ⟨n₁, hn₁, hn₁0, hcn₁, hrefl⟩ := cprime_reflA (h.act_mem_Oq u) (h.act_mem_Oq u') hp
  have hsum : n₁ + vapp (h.act σ₁) n₁ + vapp (h.act σ₁) (vapp (h.act σ₁) n₁) = 0 := by
    rw [hσρ]
    exact (rho_rotA hρR hρne hρfix hn₁ hn₁0).2
  obtain ⟨x, hx, hsign⟩ := h.exists_sign σ₁ (hR.pow_three hσR) n₁ hsum
  refine ⟨u, u', σ₁, x, n₁, ⟨hu, hu', hu2, hu'2, hcomm, hau, hau', hp, hσR, ?_, ?_, hn₁, hn₁0,
    hcn₁, hrefl, hx, hsign⟩⟩
  · rw [hσρ]
    exact hρne
  · intro v hv
    rw [hσρ]
    exact hρfix v hv

end Two

end CFSG.Quasithin.H13.U43
