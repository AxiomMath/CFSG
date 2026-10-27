module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153D

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem eq_c0_of_mem_c134CQ (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1)
    (hZ : ∀ v ∈ VZ T M, (∀ s ∈ Sgp153 T V₁, s * v = v * s) →
      v = 1 ∨ v = c₀ ∨ v = u₀ ∨ v = c₀ * u₀)
    {x : G} (hx : x ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hx1 : x ≠ 1)
    (hxS : ∀ s ∈ Sgp153 T V₁, s * x = x * s) : x = c₀ := by
  have hD := c.ctx.hyp.decomp
  obtain ⟨Vc', Vn', hlabel', -, hVc', -, -⟩ :=
    Stellmacher.PU.L3YC.pu_f1_f2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
  have hinf : Vc ⊓ Vn = ⊥ := by
    rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hD.inf
    · rw [inf_comm]; exact hD.inf
  have hCV : c134CQ (L ⊔ Sgp153 T V₁) L ≤ VZ T M := by
    rw [← hVc']
    rcases hlabel' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hD.le₁
    · exact hD.le₂
  have hCVc : c134CQ (L ⊔ Sgp153 T V₁) L = Vc := by
    rw [← hVc']
    have hne : Vc' ≠ Vn := by
      intro he
      apply hc₀1
      have : c₀ ∈ Vc ⊓ Vn := ⟨hc₀Vc, he ▸ hVc' ▸ hc₀⟩
      rw [hinf] at this
      exact this
    rcases hlabel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hlabel' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · rw [h1, h1']
    · exact absurd (h1'.trans h2.symm) hne
    · exact absurd (h1'.trans h2.symm) hne
    · rw [h1, h1']
  have hu₀n : ∀ y ∈ c134CQ (L ⊔ Sgp153 T V₁) L, y = u₀ → False := by
    intro y hy hyu
    apply hu₀1
    have : u₀ ∈ Vc ⊓ Vn := ⟨hCVc ▸ (hyu ▸ hy), hu₀⟩
    rw [hinf] at this
    exact this
  rcases hZ x (hCV hx) hxS with h | h | h | h
  · exact absurd h hx1
  · exact h
  · exact (hu₀n x hx h).elim
  · exfalso
    have hu : u₀ = c₀⁻¹ * x := by rw [h]; group
    exact hu₀n (c₀⁻¹ * x)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₀) hx) hu.symm

end Stellmacher.L3YC

end CFSG.Quasithin
