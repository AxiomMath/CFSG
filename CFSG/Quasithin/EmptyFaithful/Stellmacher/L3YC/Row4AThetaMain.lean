module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AThetaSetting
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AThetaGen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Transport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_singleton_of {g c : G} (h : g * c * g⁻¹ = c) :
    g ∈ Subgroup.centralizer ({c} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h' hh'
  rw [Set.mem_singleton_iff.mp hh']
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

omit [Finite G] in
theorem card_U_eq_eight {L U : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)}
    (α : ↥L →* ↥Γ) (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1) : Nat.card ↥U = 8 := by
  obtain ⟨B, -⟩ := Stellmacher.PU.L3YC.natural_coord α hnat
  rw [Nat.card_congr B.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_fintype_card, hF]
  norm_num

omit [Finite G] in
theorem inv_conj_mem_of_swap {YL YC S : Subgroup G} {t' : G} (hswap : B6.conjSub t' YL = YC)
    (hSY : S ≤ Subgroup.normalizer (YC : Set G)) (ht'2 : t' * t' ∈ S) {g : G} (hg : g ∈ YL) :
    t'⁻¹ * g * t' ∈ YC := by
  have h1 : t' * g * t'⁻¹ ∈ YC := by
    rw [← hswap, B6.mem_conjSub]
    have e : t'⁻¹ * (t' * g * t'⁻¹) * t' = g := by group
    rw [e]; exact hg
  have h2 := (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem ht'2)) _).mp h1
  have e : (t' * t')⁻¹ * (t' * g * t'⁻¹) * ((t' * t')⁻¹)⁻¹ = t'⁻¹ * g * t' := by group
  rwa [e] at h2

theorem row4a_theta (h11 : StageLemma14111) (h113 : StageLemma14113) (h37 : A37ForSQTK)
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
    ∃ Θ : Subgroup G, Θ ≠ ⊥ ∧ Θ ≤ Sgp153 T V₁ ∧ Sgp153 T V₁ ≤ Subgroup.normalizer (Θ : Set G) ∧
      L ≤ Subgroup.normalizer (Θ : Set G) ∧ YC153 Yp L ≤ Subgroup.normalizer (Θ : Set G) ∧
      L ≤ Subgroup.normalizer (B6.conjSub t' Θ : Set G) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  obtain ⟨hVcCQ, hVn4, hVnU, hVsw⟩ := factors_of_label h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S
    hswap h4 hlabel hc₀ hc₀Vc hc₀1
  obtain ⟨hS2, hPS, hQsyl, hSY, -, -⟩ := setting_facts h113 h37 h38 c hq c12 hV hYY hSL ht'T
    ht'S hswap
  obtain ⟨hC4, hCsq⟩ := c134CQ_card_four hq h4
  obtain ⟨y, x, s₁, s₂, hyY, hy3, hxL, hx3, -, hxu, hxn, -, -, -, -, -, -, -, -, -, -, -, hx₂3, -,
      hx₂c, -, -, -, -, -, -, -⟩ :=
    exists_e_x2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc hc₀1 hu₀ hu₀1
      hu₀S hsw
  obtain ⟨e, heY, heu⟩ := row4a_moving_element h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
    hc₀ hc₀1 hu₀S hsw
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hD
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hD.relIndex_nS hyp
  have ht'2 : t' * t' ∈ Sgp153 T V₁ := mul_self_mem_S hidx ht'T
  have hc₀S := centralizes_of_swap (hTS ht'T) hu₀S hsw
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb => by
    have := hyp.elemAbelian.1
    exact setLike_mul_comm ha hb
  have hVcV : Vc ≤ VZ T M := by
    rcases hlabel with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact hD.le₁
    · exact hD.le₂
  have hVc4 : Nat.card ↥Vc = 4 := by rw [hVcCQ]; exact hC4
  have hSVc : Sgp153 T V₁ ≤ Subgroup.normalizer (Vc : Set G) := by
    rcases hlabel with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact inf_le_right
    · exact Hyp153.Sgp153_le_normalizer_V₂ hyp hD
  have hLc : L ≤ Subgroup.centralizer (Vc : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [hVcCQ] at hv
    exact (Subgroup.mem_centralizer_iff.mp hv.2 l hl).symm
  have hLN : L ≤ Subgroup.normalizer (Vc : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (hLc hl)
  set H : Subgroup G := Subgroup.centralizer ({c₀} : Set G) with hHdef
  have hCH : Subgroup.centralizer (Vc : Set G) ≤ H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc₀Vc)
  have hLH : L ≤ H := hLc.trans hCH
  have hSH : Sgp153 T V₁ ≤ H := by
    intro s hs
    exact Subgroup.mem_centralizer_iff.mpr fun h hh' => by
      rw [Set.mem_singleton_iff.mp hh']
      exact (hc₀S s hs).symm
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) H :=
    row4a_sylow h11 hh ht'T hlabel hc₀Vc hc₀1 hu₀ hu₀1 hu₀S hsw
  have hRS : O2sub H ≤ Sgp153 T V₁ := O2sub_le_of_isSylow hSyl
  have hRN : O2sub H ≤ Subgroup.normalizer (Vc : Set G) := hRS.trans hSVc
  have hVH : Vc ≤ H := fun v hv => mem_centralizer_singleton_of
    (mul_inv_eq_iff_eq_mul.mpr (hVab v (hVcV hv) c₀ (hVcV hc₀Vc)))
  have hVR : Vc ≤ O2sub H := by
    intro v hv
    have hvq : v ∈ c134CQ (L ⊔ Sgp153 T V₁) L := hVcCQ ▸ hv
    exact (mem_O2sub_iff ⟨v, hVH hv⟩).mpr (hCQ v hvq (hVH hv))
  set K₁ := modO2Image H L₁ with hK₁
  have hK₁n : K₁.Normal := hL₁n.map _ (QuotientGroup.mk'_surjective _)
  have hH₁H : preImage H K₁ ≤ H := preImage_le H K₁
  have hH₁n : ∀ g ∈ H, ∀ h ∈ preImage H K₁, g⁻¹ * h * g ∈ preImage H K₁ := fun g hg h hh => by
    have := conj_mem_preImage hK₁n (H.inv_mem hg) hh
    simpa using this
  set Θ := theta (preImage H K₁) Vc with hΘ
  have hΘR : Θ ≤ O2sub H := theta_le_O2sub hH₁H hVR
  have hΘS : Θ ≤ Sgp153 T V₁ := hΘR.trans hRS
  have hNΘ : H ⊓ Subgroup.normalizer (Vc : Set G) ≤ Subgroup.normalizer (Θ : Set G) :=
    inf_normalizer_le_normalizer_theta hH₁n
  have hH₁Θ : preImage H K₁ ≤ Subgroup.normalizer (Θ : Set G) :=
    le_normalizer_theta_self _ _
  have hSΘ : Sgp153 T V₁ ≤ Subgroup.normalizer (Θ : Set G) := fun s hs => hNΘ ⟨hSH hs, hSVc hs⟩
  have hLΘ : L ≤ Subgroup.normalizer (Θ : Set G) := fun l hl => hNΘ ⟨hLH hl, hLN hl⟩
  have hCΘ : Subgroup.centralizer (Vc : Set G) ≤ Subgroup.normalizer (Θ : Set G) := fun g hg =>
    hNΘ ⟨hCH hg, Subgroup.centralizer_le_normalizer _ hg⟩
  set x₂ : G := t'⁻¹ * x * t' with hx₂def
  have hx₂H : x₂ ∈ H := mem_centralizer_singleton_of hx₂c
  have hx₂ord : (⟨x₂, hx₂H⟩ : ↥H) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one x₂
    rw [hx₂3] at this
    simpa using this
  have hx₂K : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x₂, hx₂H⟩ ∈ K₁ :=
    h3 _ ⟨1, by rw [pow_one, ← map_pow, hx₂ord, map_one]⟩
  have hx₂H₁ : x₂ ∈ preImage H K₁ := (mem_preImage_iff ⟨x₂, hx₂H⟩).mpr hx₂K
  have hx₂N : x₂ ∉ Subgroup.normalizer (Vc : Set G) := by
    intro hx₂Vc
    apply hxn
    rw [← conjSub_eq_self_iff, ← hVsw, ← B6.conjSub_mul]
    have e : x * t' = t' * x₂ := by rw [hx₂def]; group
    rw [e, B6.conjSub_mul, B6.conjSub_eq_self hx₂Vc]
  have horb := orbit_lemma hLN hRN hx₂H hx₂N hx₂K h2t
  have h4' := h4
  obtain ⟨⟨n, F, iF, iFin, α, hFc, hα, -, -, -, hnat, -, -, -⟩, -⟩ := h4'
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hU8 := card_U_eq_eight hF α hnat
  set U₀ : Subgroup G :=
    B6.conjSub t'⁻¹ ⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ with hU₀
  have hU₀8 : Nat.card ↥U₀ = 8 := (card_conjSub _ _).trans hU8
  have hVn_swap : B6.conjSub t'⁻¹ Vn = Vc := by
    rw [← hVsw, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have hVU₀ : Vc ≤ U₀ := by
    have := (B6.conjSub t'⁻¹).monotone hVnU
    rwa [hVn_swap] at this
  have hxU₀ : x₂ ∈ Subgroup.normalizer (U₀ : Set G) := by
    rw [hU₀, mem_normalizer_conjSub_iff]
    have e : (t'⁻¹)⁻¹ * x₂ * t'⁻¹ = x := by rw [hx₂def]; group
    rw [e]
    exact hnat.1 hxL
  have hcU : B6.conjSub x₂ Vc ≤ U₀ := by
    have := (B6.conjSub x₂).monotone hVU₀
    rwa [B6.conjSub_eq_self hxU₀] at this
  have hUΘ : U₀ ≤ Θ := U_le_theta hVc4 hU₀8 hVU₀ hxU₀ hx₂N hx₂H₁
  have hYC : YC153 Yp L ≤ Subgroup.normalizer (Θ : Set G) := by
    intro y hy
    have hyV : y ∈ Subgroup.normalizer (Vc : Set G) := by
      rw [hVcCQ]
      exact (N0_le_normalizer hSL h4 (YC_le_N0 hy)).2
    have hyL : t'⁻¹ * y * t' ∈ L := by
      have : t'⁻¹ * y * t' ∈ YL153 Yp L := by
        rw [← hswap] at hy
        exact B6.mem_conjSub.mp hy
      exact (oTwoUpper_le _ this).2
    have hyU : y ∈ Subgroup.normalizer (U₀ : Set G) := by
      rw [hU₀, mem_normalizer_conjSub_iff, inv_inv]
      have : t' * y * t'⁻¹ ∈ L := by
        have e : t' * y * t'⁻¹ = (t' * t') * (t'⁻¹ * y * t') * (t' * t')⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hSL ht'2) _).mp hyL
      exact hnat.1 this
    exact normalizer_theta_of_acts hVU₀ hcU hUΘ horb hLc hCΘ hyV hyU
  have hLΘ' : L ≤ Subgroup.normalizer (B6.conjSub t' Θ : Set G) := by
    have hyL' : ∀ g ∈ YL153 Yp L, g ∈ Subgroup.normalizer (B6.conjSub t' Θ : Set G) := by
      intro g hg
      rw [mem_normalizer_conjSub_iff]
      exact hYC (inv_conj_mem_of_swap hswap hSY ht'2 hg)
    refine le_of_gen hF α hα hnat hQsyl hPS (hVnU hu₀) hu₀1
      (fun s hs => mul_inv_eq_iff_eq_mul.mpr (hu₀S s hs.1)) (fun s hs => ?_) hxL hx3 hxu ?_
      ((oTwoUpper_le _ heY).2) (hyL' e heY) heu
    · rw [mem_normalizer_conjSub_iff]
      exact hSΘ ((Subgroup.mem_normalizer_iff''.mp (hTS ht'T) s).mp hs.1)
    · rw [mem_normalizer_conjSub_iff]
      exact hH₁Θ hx₂H₁
  refine ⟨Θ, ?_, hΘS, hSΘ, hLΘ, hYC, hLΘ'⟩
  intro h0
  have hVb : Vc ≤ ⊥ := h0 ▸ (le_theta : Vc ≤ theta (preImage H K₁) Vc)
  have := Subgroup.card_bot (G := G)
  rw [le_bot_iff.mp hVb] at hVc4
  omega

end Main

end Stellmacher.L3YC

end CFSG.Quasithin
