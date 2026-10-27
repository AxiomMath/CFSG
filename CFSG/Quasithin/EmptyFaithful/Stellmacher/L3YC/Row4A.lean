module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AFinal
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AStep1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AStep2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4AMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S153D

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem row4a_false
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hc₀2 : c₀ * c₀ = 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀) {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hL₁n : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal)
    {P : Subgroup (↥(Subgroup.centralizer ({c₀} : Set G)) ⧸
      CFSG.pCore 2 ↥(Subgroup.centralizer ({c₀} : Set G)))}
    (h42 : IsPSL 4 2 1 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁))
    (hpar : IsParabolic2 (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁) P)
    (hBP : modO2Image (Subgroup.centralizer ({c₀} : Set G)) L = perfectCore P) : False := by
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ Subgroup.centralizer ({c₀} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  have hev : CFSG.Assembly.evenRank G ≤ 2 := c.ctx.hyp.hyp.qtfe.qtke.2.2
  have hCQ := (row4a_cq_le_pCore hLH hLL₁ le_sup_left (CD.L3YC.sup_le_normalizer hSL) hq hperf h4
    h42).2
  have h3 := row4a_three_mem_centralizer hc₀1 hc₀2 hev hL₁n h42
  have hB3 : IsPSL 3 2 1 (ModO2 (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)) :=
    CD.L3YC.isPSL_modO2_modO2Image hLH hq
  have h2t := (Stellmacher.PU.L3YC.l4_parabolic_data h42 hpar hBP hB3).2.2
  exact row4a_false_of h11 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc
    hc₀1 hu₀ hu₀1 hu₀S hsw hL₁n hCQ h3 h2t

end Stellmacher.L3YC

end CFSG.Quasithin
