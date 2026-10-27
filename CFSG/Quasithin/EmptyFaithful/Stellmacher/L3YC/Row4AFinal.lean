module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AThetaMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AThetaW

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Final

variable {G : Type} [Group G] [Finite G]

theorem row4a_exists_W (h11 : StageLemma14111) (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀) {L₁ : Subgroup G}
    (hL₁n : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal)
    (hCQ : ∀ v ∈ c134CQ (L ⊔ Sgp153 T V₁) L, ∀ hv : v ∈ Subgroup.centralizer ({c₀} : Set G),
      (⟨v, hv⟩ : ↥(Subgroup.centralizer ({c₀} : Set G))) ∈
        CFSG.pCore 2 ↥(Subgroup.centralizer ({c₀} : Set G)))
    (h3 : ∀ g : ↥(Subgroup.centralizer ({c₀} : Set G)) ⧸
        CFSG.pCore 2 ↥(Subgroup.centralizer ({c₀} : Set G)),
      (∃ m : ℕ, g ^ 3 ^ m = 1) → g ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)
    (h2t : ∀ g ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁,
      g ∉ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L → ∀ h ∈ modO2Image
        (Subgroup.centralizer ({c₀} : Set G)) L₁,
      h ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L ∨
        ∃ a ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L,
          ∃ b ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L, h = a * g * b) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 ↥W ∧ L ≤ Subgroup.normalizer (W : Set G) ∧
      T ≤ Subgroup.normalizer (W : Set G) ∧
      Y153 Mc M ≤ Subgroup.normalizer (W : Set G) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  obtain ⟨hS2, hPS, hQsyl, hSY, -, -⟩ := setting_facts h113 h37 h38 c hq c12 hV hYY hSL ht'T
    ht'S hswap
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hD
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hD.relIndex_nS hyp
  obtain ⟨Θ, hΘ0, hΘS, hSΘ, hLΘ, hYCΘ, hLΘ'⟩ := row4a_theta h11 h113 h37 h38 c hq c12 hV hYY hSL
    ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc hc₀1 hu₀ hu₀1 hu₀S hsw hL₁n hCQ h3 h2t
  have hYLL : YL153 Yp L ≤ L := fun y hy => (oTwoUpper_le _ hy).2
  rw [← hYY]
  exact exists_W_of_theta hS2 hTS hidx ht'T ht'S hΘ0 hΘS hSΘ hLΘ hYCΘ hLΘ' hswap hYLL hSY c12.1

theorem row4a_false_of (h11 : StageLemma14111) (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀) {L₁ : Subgroup G}
    (hL₁n : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal)
    (hCQ : ∀ v ∈ c134CQ (L ⊔ Sgp153 T V₁) L, ∀ hv : v ∈ Subgroup.centralizer ({c₀} : Set G),
      (⟨v, hv⟩ : ↥(Subgroup.centralizer ({c₀} : Set G))) ∈
        CFSG.pCore 2 ↥(Subgroup.centralizer ({c₀} : Set G)))
    (h3 : ∀ g : ↥(Subgroup.centralizer ({c₀} : Set G)) ⧸
        CFSG.pCore 2 ↥(Subgroup.centralizer ({c₀} : Set G)),
      (∃ m : ℕ, g ^ 3 ^ m = 1) → g ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)
    (h2t : ∀ g ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁,
      g ∉ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L → ∀ h ∈ modO2Image
        (Subgroup.centralizer ({c₀} : Set G)) L₁,
      h ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L ∨
        ∃ a ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L,
          ∃ b ∈ modO2Image (Subgroup.centralizer ({c₀} : Set G)) L, h = a * g * b) :
    False := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  obtain ⟨W, hW0, hW2, hWL, hWT, hWY⟩ := row4a_exists_W h11 h113 h37 h38 c hq c12 hV hYY hSL ht'T
    ht'S hswap h4 hlabel hc₀ hc₀Vc hc₀1 hu₀ hu₀1 hu₀S hsw hL₁n hCQ h3 h2t
  have hLc : L ∈ cComp (thompsonJ I) := c.toCtx15313L.conc.1
  have hLn : ¬ L ≤ M ⊓ I := c.toCtx15313L.conc.2.1
  have hLle : L ≤ I := le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ hLc)
  have hCO : W ≤ pCoreOf 2 (Subgroup.normalizer (W : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hW2
  have hXN : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (W : Set G) := sup_le hWY hWT
  have hH : InH (Y153 Mc M ⊔ T) (Subgroup.normalizer (W : Set G)) :=
    ⟨hXN, fun hb => hW0 (le_bot_iff.mp (hb ▸ hCO))⟩
  have hNM : Subgroup.normalizer (W : Set G) ≤ M :=
    le_of_isUniqueM (Hyp153.lemma_15_3_7_unique h113 hh.hyp) hH
  exact hLn (le_inf (hWL.trans hNM) hLle)

end Final

end Stellmacher.L3YC

end CFSG.Quasithin
