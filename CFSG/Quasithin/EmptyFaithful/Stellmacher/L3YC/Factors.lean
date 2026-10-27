module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Setting

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem factors_of_label (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1) :
    Vc = c134CQ (L ⊔ Sgp153 T V₁) L ∧ Nat.card ↥Vn = 4 ∧
      Vn ≤ ⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ ∧ B6.conjSub t' Vc = Vn := by
  classical
  obtain ⟨Vc', Vn', hlabel', -, hVcCQ, -, hF2U⟩ :=
    Stellmacher.PU.L3YC.pu_f1_f2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  obtain ⟨hsw1, hsw2⟩ := szN3_conj_V_swap hyp hD ht'T ht'S
  have hc₀' : c₀ ∈ Vc' := hVcCQ ▸ hc₀
  have hdisj : ∀ x ∈ V₁, x ∈ V₂ → x = 1 := fun x h1 h2 => by
    have : x ∈ V₁ ⊓ V₂ := ⟨h1, h2⟩
    rw [hD.inf, Subgroup.mem_bot] at this
    exact this
  rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hlabel' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hVcCQ, hD.card₂, hF2U, hsw1⟩
  · exact absurd (hdisj c₀ hc₀Vc hc₀') hc₀1
  · exact absurd (hdisj c₀ hc₀' hc₀Vc) hc₀1
  · exact ⟨hVcCQ, hD.card₁, hF2U, hsw2⟩

end Setting

end Stellmacher.L3YC

end CFSG.Quasithin
