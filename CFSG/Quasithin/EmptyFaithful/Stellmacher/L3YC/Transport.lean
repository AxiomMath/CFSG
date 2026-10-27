module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Thm1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_e_x2 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀) :
    ∃ y x s₁ s₂ : G, y ∈ YC153 Yp L ∧ orderOf y = 3 ∧ x ∈ L ∧ orderOf x = 3 ∧ x * y = y * x ∧
      x * u₀ * x⁻¹ = u₀ ∧ x ∉ Subgroup.normalizer (Vn : Set G) ∧
      s₁ ∈ Sgp153 T V₁ ∧ s₂ ∈ Sgp153 T V₁ ∧ (∃ k : ℕ, s₁ ^ 2 ^ k = 1) ∧ (∃ k : ℕ, s₂ ^ 2 ^ k = 1) ∧
      s₁ * y * s₁⁻¹ = y⁻¹ ∧ s₁ * x * s₁⁻¹ = x ∧ s₂ * x * s₂⁻¹ = x⁻¹ ∧ s₂ * y * s₂⁻¹ = y ∧
      t'⁻¹ * y * t' ∈ YL153 Yp L ∧ t'⁻¹ * y * t' ∈ L ∧ orderOf (t'⁻¹ * y * t') = 3 ∧
      orderOf (t'⁻¹ * x * t') = 3 ∧
      (t'⁻¹ * y * t') * (t'⁻¹ * x * t') = (t'⁻¹ * x * t') * (t'⁻¹ * y * t') ∧
      (t'⁻¹ * x * t') * c₀ * (t'⁻¹ * x * t')⁻¹ = c₀ ∧
      t'⁻¹ * x * t' ∉ Subgroup.normalizer (L : Set G) ∧
      t'⁻¹ * s₁ * t' ∈ Sgp153 T V₁ ∧ t'⁻¹ * s₂ * t' ∈ Sgp153 T V₁ ∧
      (t'⁻¹ * s₁ * t') * (t'⁻¹ * y * t') * (t'⁻¹ * s₁ * t')⁻¹ = (t'⁻¹ * y * t')⁻¹ ∧
      (t'⁻¹ * s₁ * t') * (t'⁻¹ * x * t') * (t'⁻¹ * s₁ * t')⁻¹ = t'⁻¹ * x * t' ∧
      (t'⁻¹ * s₂ * t') * (t'⁻¹ * x * t') * (t'⁻¹ * s₂ * t')⁻¹ = (t'⁻¹ * x * t')⁻¹ ∧
      (t'⁻¹ * s₂ * t') * (t'⁻¹ * y * t') * (t'⁻¹ * s₂ * t')⁻¹ = t'⁻¹ * y * t' := by
  classical
  obtain ⟨hVcCQ, -, -, hVsw⟩ := factors_of_label h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
    hlabel hc₀ hc₀Vc hc₀1
  obtain ⟨y, x, s₁, s₂, hyY, hy3, hxL, hx3, hxy, hxu, hxn, hs₁S, hs₂S, h2₁, h2₂, hs₁y, hs₁x, hs₂x,
      hs₂y⟩ :=
    exists_elements_thm1 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc hc₀1
      hu₀ hu₀1 hu₀S
  have hyL : t'⁻¹ * y * t' ∈ YL153 Yp L := by
    rw [← hswap] at hyY
    exact (B6.mem_conjSub).mp hyY
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hh.hyp hh.decomp
  have hconjS : ∀ s ∈ Sgp153 T V₁, t'⁻¹ * s * t' ∈ Sgp153 T V₁ := fun s hs =>
    (Subgroup.mem_normalizer_iff''.mp (hTS ht'T) s).mp hs
  refine ⟨y, x, s₁, s₂, hyY, hy3, hxL, hx3, hxy, hxu, hxn, hs₁S, hs₂S, h2₁, h2₂, hs₁y, hs₁x, hs₂x,
    hs₂y, hyL, ((oTwoUpper_le _) hyL).2, ?_, ?_, ?_, ?_, ?_, hconjS _ hs₁S, hconjS _ hs₂S, ?_, ?_,
    ?_, ?_⟩
  · have := orderOf_conj_eq t'⁻¹ y
    rw [inv_inv] at this
    rw [this, hy3]
  · have := orderOf_conj_eq t'⁻¹ x
    rw [inv_inv] at this
    rw [this, hx3]
  · calc (t'⁻¹ * y * t') * (t'⁻¹ * x * t') = t'⁻¹ * (y * x) * t' := by group
      _ = t'⁻¹ * (x * y) * t' := by rw [hxy.symm]
      _ = (t'⁻¹ * x * t') * (t'⁻¹ * y * t') := by group
  · have hu : t'⁻¹ * u₀ * t' = c₀ := by rw [← hsw]; group
    calc (t'⁻¹ * x * t') * c₀ * (t'⁻¹ * x * t')⁻¹
        = t'⁻¹ * (x * (t' * c₀ * t'⁻¹) * x⁻¹) * t' := by group
      _ = c₀ := by rw [hsw, hxu, hu]
  · have hGL : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Vc : Set G) := by
      rw [hVcCQ]
      exact Stellmacher.CD.L3YC.normalizer_le_normalizer_c134CQ_of_case4 hSL h4
    exact Stellmacher.CD.L3YC.conj_not_mem_normalizer hGL hVsw hxn
  · calc (t'⁻¹ * s₁ * t') * (t'⁻¹ * y * t') * (t'⁻¹ * s₁ * t')⁻¹
        = t'⁻¹ * (s₁ * y * s₁⁻¹) * t' := by group
      _ = t'⁻¹ * y⁻¹ * t' := by rw [hs₁y]
      _ = (t'⁻¹ * y * t')⁻¹ := by group
  · calc (t'⁻¹ * s₁ * t') * (t'⁻¹ * x * t') * (t'⁻¹ * s₁ * t')⁻¹
        = t'⁻¹ * (s₁ * x * s₁⁻¹) * t' := by group
      _ = t'⁻¹ * x * t' := by rw [hs₁x]
  · calc (t'⁻¹ * s₂ * t') * (t'⁻¹ * x * t') * (t'⁻¹ * s₂ * t')⁻¹
        = t'⁻¹ * (s₂ * x * s₂⁻¹) * t' := by group
      _ = t'⁻¹ * x⁻¹ * t' := by rw [hs₂x]
      _ = (t'⁻¹ * x * t')⁻¹ := by group
  · calc (t'⁻¹ * s₂ * t') * (t'⁻¹ * y * t') * (t'⁻¹ * s₂ * t')⁻¹
        = t'⁻¹ * (s₂ * y * s₂⁻¹) * t' := by group
      _ = t'⁻¹ * y * t' := by rw [hs₂y]

end Main

end Stellmacher.L3YC

end CFSG.Quasithin
