module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.PU.L3YC

section Core

variable {G : Type} [Group G] [Finite G]

theorem swap_core {S V Vc Vn : Subgroup G} {t' : G} (hS2 : IsPGroup 2 ↥S) (hVS : V ≤ S)
    (hVc : Vc ≤ V) (hinf : Vc ⊓ Vn = ⊥) (hc4 : Nat.card Vc = 4) (hsqV : ∀ a ∈ V, a * a = 1)
    (hSc : S ≤ Subgroup.normalizer (Vc : Set G))
    (hZ4 : Nat.card ↥(V ⊓ Subgroup.centralizer (S : Set G)) = 4)
    (ht'N : t' ∈ Subgroup.normalizer (S : Set G)) (ht'2 : t' * t' ∈ S)
    (hswc : ∀ x ∈ Vc, t' * x * t'⁻¹ ∈ Vn) (hVn : Vn ≤ V) :
    ∃ c₀ u₀ : G, c₀ ∈ Vc ∧ u₀ ∈ Vn ∧ c₀ ≠ 1 ∧ u₀ ≠ 1 ∧ c₀ * c₀ = 1 ∧ u₀ * u₀ = 1 ∧
      (∀ s ∈ S, s * c₀ = c₀ * s ∧ s * u₀ = u₀ * s) ∧
      t' * c₀ * t'⁻¹ = u₀ ∧ t' * u₀ * t'⁻¹ = c₀ ∧
      (∀ v ∈ V, (∀ s ∈ S, s * v = v * s) → v = 1 ∨ v = c₀ ∨ v = u₀ ∨ v = c₀ * u₀) := by
  classical
  have hVc1 : Vc ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc4
    omega
  obtain ⟨c₀, hc₀, hc₀1, hc₀2, hc₀S⟩ :=
    SzC4.exists_fixed_involution hS2 (hVc.trans hVS) hSc hVc1 (fun e he => hsqV e (hVc he))
  have hu₀n : t' * c₀ * t'⁻¹ ∈ Vn := hswc c₀ hc₀
  have hu₀1 : t' * c₀ * t'⁻¹ ≠ 1 := by
    intro h
    apply hc₀1
    calc c₀ = t'⁻¹ * (t' * c₀ * t'⁻¹) * t' := by group
      _ = 1 := by rw [h]; group
  have hu₀2 : (t' * c₀ * t'⁻¹) * (t' * c₀ * t'⁻¹) = 1 := by
    calc (t' * c₀ * t'⁻¹) * (t' * c₀ * t'⁻¹) = t' * (c₀ * c₀) * t'⁻¹ := by group
      _ = 1 := by rw [hc₀2]; group
  have hu₀S : ∀ s ∈ S, s * (t' * c₀ * t'⁻¹) = (t' * c₀ * t'⁻¹) * s := by
    intro s hs
    have h1 : t'⁻¹ * s * t' ∈ S := (Subgroup.mem_normalizer_iff''.mp ht'N s).mp hs
    have h2 := hc₀S _ h1
    calc s * (t' * c₀ * t'⁻¹) = t' * ((t'⁻¹ * s * t') * c₀) * t'⁻¹ := by group
      _ = t' * (c₀ * (t'⁻¹ * s * t')) * t'⁻¹ := by rw [h2]
      _ = (t' * c₀ * t'⁻¹) * s := by group
  have hcZ : c₀ ∈ V ⊓ Subgroup.centralizer (S : Set G) :=
    ⟨hVc hc₀, Subgroup.mem_centralizer_iff.mpr hc₀S⟩
  have huZ : t' * c₀ * t'⁻¹ ∈ V ⊓ Subgroup.centralizer (S : Set G) :=
    ⟨hVn hu₀n, Subgroup.mem_centralizer_iff.mpr hu₀S⟩
  have hne : c₀ ≠ t' * c₀ * t'⁻¹ := by
    intro heq
    have hmem : c₀ ∈ Vc ⊓ Vn := ⟨hc₀, heq ▸ hu₀n⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hc₀1 hmem
  have hmul : c₀ * (t' * c₀ * t'⁻¹) ≠ 1 := by
    intro h
    apply hne
    exact (eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hu₀2)
  refine ⟨c₀, t' * c₀ * t'⁻¹, hc₀, hu₀n, hc₀1, hu₀1, hc₀2, hu₀2,
    fun s hs => ⟨hc₀S s hs, hu₀S s hs⟩, rfl, ?_, ?_⟩
  · calc t' * (t' * c₀ * t'⁻¹) * t'⁻¹ = (t' * t') * c₀ * (t' * t')⁻¹ := by group
      _ = c₀ := by rw [hc₀S _ ht'2]; group
  · intro v hv hvS
    exact SzC4.mem_of_card_four hZ4 hcZ huZ hc₀1 hu₀1 hne hmul v
      ⟨hv, Subgroup.mem_centralizer_iff.mpr hvS⟩

end Core

theorem pu_f5_f6 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L) :
    ∃ Vc Vn : Subgroup G, ∃ c₀ u₀ : G, ((Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁)) ∧
      c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L ∧
      u₀ ∈ ⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ ∧
      c₀ ∈ Vc ∧ u₀ ∈ Vn ∧ c₀ ≠ 1 ∧ u₀ ≠ 1 ∧ c₀ * c₀ = 1 ∧ u₀ * u₀ = 1 ∧
      (∀ s ∈ Sgp153 T V₁, s * c₀ = c₀ * s ∧ s * u₀ = u₀ * s) ∧
      t' * c₀ * t'⁻¹ = u₀ ∧ t' * u₀ * t'⁻¹ = c₀ ∧
      (∀ v ∈ VZ T M, (∀ s ∈ Sgp153 T V₁, s * v = v * s) →
        v = 1 ∨ v = c₀ ∨ v = u₀ ∨ v = c₀ * u₀) := by
  classical
  obtain ⟨Vc, Vn, hlabel, -, hVcCQ, -, hF2U⟩ :=
    pu_f1_f2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hVS : VZ T M ≤ Sgp153 T V₁ := VZ_le_Sgp153 hh
  have hsqV : ∀ a ∈ VZ T M, a * a = 1 := fun a ha => by
    have := hyp.elemAbelian.2 a ha
    rw [pow_two] at this
    exact this
  have hZ4 := (hyp.lemma_15_3_8 hD).2
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hD
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hD.relIndex_nS hyp
  have ht'2 : t' * t' ∈ Sgp153 T V₁ := by
    have h2 : ((Sgp153 T V₁).subgroupOf T).index = 2 := hidx
    have h3 := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨t', ht'T⟩) (b := ⟨t', ht'T⟩)
    have hiff : (⟨t', ht'T⟩ * ⟨t', ht'T⟩ : ↥T) ∈ (Sgp153 T V₁).subgroupOf T := by
      rw [h3]
    exact hiff
  obtain ⟨hsw1, hsw2⟩ := szN3_conj_V_swap hyp hD ht'T ht'S
  have hconj : ∀ A B : Subgroup G, B6.conjSub t' A = B → ∀ x ∈ A, t' * x * t'⁻¹ ∈ B := by
    intro A B h x hx
    rw [← h, B6.mem_conjSub]
    have e : t'⁻¹ * (t' * x * t'⁻¹) * t' = x := by group
    rw [e]
    exact hx
  have hSV₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    Hyp153.Sgp153_le_normalizer_V₂ hyp hD
  rcases hlabel with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hVcCQ' : V₁ = c134CQ (L ⊔ Sgp153 T V₁) L := h1.symm.trans hVcCQ
    have hF2U' : V₂ ≤ ⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ := by have h := hF2U; rwa [h2] at h
    obtain ⟨c₀, u₀, hc₀, hu₀, e1, e2, e3, e4, hS, hsw, hsw', hZ⟩ :=
      swap_core hS2 hVS hD.le₁ hD.inf hD.card₁ hsqV hSV₁ hZ4 (hTS ht'T) ht'2
        (hconj _ _ hsw1) hD.le₂
    exact ⟨V₁, V₂, c₀, u₀, Or.inl ⟨rfl, rfl⟩, hVcCQ' ▸ hc₀, hF2U' hu₀, hc₀, hu₀, e1, e2, e3,
      e4, hS, hsw, hsw', hZ⟩
  · have hVcCQ' : V₂ = c134CQ (L ⊔ Sgp153 T V₁) L := h1.symm.trans hVcCQ
    have hF2U' : V₁ ≤ ⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ := by have h := hF2U; rwa [h2] at h
    obtain ⟨c₀, u₀, hc₀, hu₀, e1, e2, e3, e4, hS, hsw, hsw', hZ⟩ :=
      swap_core hS2 hVS hD.le₂ (by rw [inf_comm]; exact hD.inf) hD.card₂ hsqV hSV₂ hZ4
        (hTS ht'T) ht'2 (hconj _ _ hsw2) hD.le₁
    exact ⟨V₂, V₁, c₀, u₀, Or.inr ⟨rfl, rfl⟩, hVcCQ' ▸ hc₀, hF2U' hu₀, hc₀, hu₀, e1, e2, e3,
      e4, hS, hsw, hsw', hZ⟩

end Stellmacher.PU.L3YC

end CFSG.Quasithin
