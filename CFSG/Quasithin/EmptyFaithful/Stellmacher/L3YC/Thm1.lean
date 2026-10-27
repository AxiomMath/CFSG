module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Factors
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.SettingY
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.ExistsX
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.StepA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.S1S2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.SettingFacts
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.ImageSylow

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_elements_thm1 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s) :
    ∃ y x s₁ s₂ : G, y ∈ YC153 Yp L ∧ orderOf y = 3 ∧ x ∈ L ∧ orderOf x = 3 ∧ x * y = y * x ∧
      x * u₀ * x⁻¹ = u₀ ∧ x ∉ Subgroup.normalizer (Vn : Set G) ∧
      s₁ ∈ Sgp153 T V₁ ∧ s₂ ∈ Sgp153 T V₁ ∧ (∃ k : ℕ, s₁ ^ 2 ^ k = 1) ∧ (∃ k : ℕ, s₂ ^ 2 ^ k = 1) ∧
      s₁ * y * s₁⁻¹ = y⁻¹ ∧ s₁ * x * s₁⁻¹ = x ∧ s₂ * x * s₂⁻¹ = x⁻¹ ∧ s₂ * y * s₂⁻¹ = y := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  obtain ⟨hVcCQ, hVn4, hVnU, -⟩ := factors_of_label h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap
    h4 hlabel hc₀ hc₀Vc hc₀1
  obtain ⟨hS2, hPS, hQsyl, hSY, hY3, hodd⟩ := setting_facts h113 h37 h38 c hq c12 hV hYY hSL ht'T
    ht'S hswap
  obtain ⟨y₀, hy₀Y, hy₀N, hy₀3, hy₀v⟩ := exists_y_order_three h113 h37 h38 c hq c12 hV hYY hSL ht'T
    ht'S hswap h4
  obtain ⟨hC4, hCsq⟩ := c134CQ_card_four hq h4
  have hSVn : Sgp153 T V₁ ≤ Subgroup.normalizer (Vn : Set G) := by
    rcases hlabel with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact Hyp153.Sgp153_le_normalizer_V₂ hyp hD
    · exact inf_le_right
  have hNV : N0 L ≤ Subgroup.normalizer (Vc : Set G) := by
    rw [hVcCQ]; exact fun g hg => (N0_le_normalizer hSL h4 hg).2
  have hVc4 : Nat.card ↥Vc = 4 := by rw [hVcCQ]; exact hC4
  have hVcsq : ∀ v ∈ Vc, v * v = 1 := by rw [hVcCQ]; exact hCsq
  have hVnV : Vn ≤ VZ T M := by
    rcases hlabel with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact hD.le₂
    · exact hD.le₁
  have hVcV : Vc ≤ VZ T M := by
    rcases hlabel with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact hD.le₁
    · exact hD.le₂
  have hVcVn : ∀ v ∈ Vc, v ∈ Vn → v = 1 := by
    intro v h1 h2
    rcases hlabel with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1] at h1; rw [e2] at h2
      have : v ∈ V₁ ⊓ V₂ := ⟨h1, h2⟩
      rw [hD.inf, Subgroup.mem_bot] at this
      exact this
    · rw [e1] at h1; rw [e2] at h2
      have : v ∈ V₁ ⊓ V₂ := ⟨h2, h1⟩
      rw [hD.inf, Subgroup.mem_bot] at this
      exact this
  obtain ⟨r₀, hr₀S, hr₀N, hr₀v⟩ : ∃ r₀ ∈ Sgp153 T V₁, r₀ ∈ N0 L ∧
      ∃ v ∈ Vc, r₀ * v * r₀⁻¹ ≠ v := by
    obtain ⟨s, hs, v, hv, hsv⟩ : ∃ s ∈ Sgp153 T V₁, ∃ v ∈ Vc, s * v * s⁻¹ ≠ v := by
      by_contra hcon
      push Not at hcon
      have hVcC : Vc ≤ VZ T M ⊓ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) := by
        intro v hv
        refine ⟨hVcV hv, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
        exact mul_inv_eq_iff_eq_mul.mp (hcon s hs v hv)
      have hZ4 := (hyp.lemma_15_3_8 hD).2
      have heq := Subgroup.eq_of_le_of_card_ge hVcC (by rw [hZ4, hVc4])
      have hu₀Z : u₀ ∈ VZ T M ⊓ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) :=
        ⟨hVnV hu₀, Subgroup.mem_centralizer_iff.mpr fun s hs => hu₀S s hs⟩
      rw [← heq] at hu₀Z
      exact hu₀1 (hVcVn u₀ hu₀Z hu₀)
    obtain ⟨p, hp, c', hc'S, hc', rfl⟩ := Stellmacher.PU.L3YC.pu_S_split c hq hSL h4 s hs
    refine ⟨c', hc'S, ⟨hSL hc'S, fun x hx => ?_⟩, v, hv, fun hcv => hsv ?_⟩
    · obtain ⟨m, hm, hmx⟩ := hc' x hx
      have : c' * x * c'⁻¹ * x⁻¹ = x * m * x⁻¹ := by rw [hmx]
      rw [this]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hx) m).mp hm
    · have hpL : (p : G) ∈ L := (Subgroup.mem_inf.mp hp).2
      have hvC : v ∈ Subgroup.centralizer (L : Set G) := by
        have : v ∈ c134CQ (L ⊔ Sgp153 T V₁) L := hVcCQ ▸ hv
        exact this.2
      have hpv : p * v = v * p := Subgroup.mem_centralizer_iff.mp hvC p hpL
      calc p * c' * v * (p * c')⁻¹ = p * (c' * v * c'⁻¹) * p⁻¹ := by group
        _ = p * v * p⁻¹ := by rw [hcv]
        _ = v := by rw [hpv]; group
  have hYV : YC153 Yp L ≤ Subgroup.normalizer (Vc : Set G) := fun y hy => hNV (YC_le_N0 hy)
  have hy₀v' : ∃ v ∈ Vc, y₀ * v * y₀⁻¹ ≠ v := by
    obtain ⟨v, hv, hne⟩ := hy₀v
    exact ⟨v, by rw [hVcCQ]; exact hv, hne⟩
  obtain ⟨y, hyY, hy3, hyv, r₁, hr₁, hr₁y⟩ := exists_inverting_pair (Y := YC153 Yp L)
    (S := Sgp153 T V₁) (M := N0 L) (V := Vc) hVc4 hVcsq YC_le_N0 hSY hYV hNV hS2 YC_gen hY3 hodd
    hy₀Y hy₀3 hy₀v' hr₀S hr₀N hr₀v
  have hyN : y ∈ N0 L := YC_le_N0 hyY
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨n, F, iF, fF, α, hFc, hα, hE2, -, -, hnat, -, -, -⟩ := h4.1
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  obtain ⟨B, W', a', hB, hW'card, ha'W, ha'0, hmemW', hBa⟩ := coord_data α hnat hVnU hVn4 hu₀ hu₀1
  obtain ⟨g, b, hg3, hga, ⟨w', hw'W, hgw'⟩, hba, hbW, hbg, hD'⟩ :=
    exists_flag_data hF hW'card ha'W ha'0
  have hgmem : g ∈ StatedSL 3 F := by
    rw [Stellmacher.PU.L3YC.statedSL_eq_top_of_card_two hF]; trivial
  obtain ⟨x, hxo, hxy, hxα⟩ := exists_order_three_lift hq α hα hyN hy3'
    (xb := ⟨g, hgmem⟩) (by rw [Subgroup.orderOf_mk]; exact hg3)
  obtain ⟨hxu, w, hwV, hxw⟩ := conj_facts α hnat hVnU hu₀ B W' a' hB hmemW' hBa g x
    (by rw [hxα]) hga hw'W hgw'
  have hxb : orderOf (α ⟨(x : G), x.2⟩) = 3 := by
    show orderOf (α x) = 3
    rw [hxα, Subgroup.orderOf_mk]; exact hg3
  obtain ⟨s₁, hs₁S, hs₁y, hs₁x⟩ := exists_s1 hq α hα hPS hSL x.2 hxo hxy.symm hxb hr₁.1 hr₁.2 hr₁y
  have hcardD := card_image_sylow_eight (S := Sgp153 T V₁) hF α hα.1 hQsyl
  have hDcond : ∀ h ∈ ((Sgp153 T V₁ ⊓ L).subgroupOf L).map ((StatedSL 3 F).subtype.comp α),
      glAct h a' = a' ∧ ∀ w ∈ W', glAct h w ∈ W' := by
    rintro h ⟨l', hl', rfl⟩
    have hl'S : (l' : G) ∈ Sgp153 T V₁ :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl')).1
    have hLU := hnat.1 l'.2
    refine ⟨?_, ?_⟩
    · have hu₀U := hVnU hu₀
      have h1 := hB l' ⟨u₀, hu₀U⟩ ⟨u₀, hu₀U⟩ (by
        show u₀ = (l' : G) * u₀ * (l' : G)⁻¹
        have := hu₀S l' hl'S
        calc u₀ = u₀ * (l' : G) * (l' : G)⁻¹ := by group
          _ = (l' : G) * u₀ * (l' : G)⁻¹ := by rw [this])
      rw [hBa hu₀U] at h1
      exact h1.symm
    · intro w hw
      obtain ⟨u, hu⟩ := B.surjective (Multiplicative.ofAdd w)
      have hu' : Multiplicative.toAdd (B u) = w := by rw [hu]; rfl
      have huVn : (u : G) ∈ Vn := (hmemW' u).mp (by rw [hu']; exact hw)
      have hvU : (l' : G) * u * (l' : G)⁻¹ ∈ _ := (Subgroup.mem_normalizer_iff.mp hLU u).mp u.2
      have h1 := hB l' u ⟨_, hvU⟩ rfl
      rw [hu'] at h1
      have hvVn : (l' : G) * u * (l' : G)⁻¹ ∈ Vn :=
        (Subgroup.mem_normalizer_iff.mp (hSVn hl'S) u).mp huVn
      have h2 := (hmemW' ⟨_, hvU⟩).mpr hvVn
      rw [h1] at h2
      exact h2
  have hbD := hD' _ hcardD hDcond
  obtain ⟨l', hl', hl'b⟩ := hbD
  have hl'S : (l' : G) ∈ Sgp153 T V₁ :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl')).1
  obtain ⟨p, hpP, hcomm⟩ := exists_mem_centralizer_coset hyN hy3' l'.2
  obtain ⟨p', hp'e, hp'1⟩ := exists_mem_ker_of_mem_pCoreOf hα hpP
  have hmS : (l' : G) * p ∈ Sgp153 T V₁ := (Sgp153 T V₁).mul_mem hl'S (hPS hpP)
  have hmL : (l' : G) * p ∈ L := L.mul_mem l'.2 (pCoreOf_le 2 L hpP)
  have hmy : (l' : G) * p * y = y * ((l' : G) * p) := hcomm.symm
  have hmα : α ⟨(l' : G) * p, hmL⟩ = α l' := by
    have : (⟨(l' : G) * p, hmL⟩ : ↥L) = l' * p' := Subtype.ext (by simp [hp'e])
    rw [this, map_mul, hp'1, mul_one]
  have hmx : α ⟨(l' : G) * p, hmL⟩ * α ⟨(x : G), x.2⟩ * (α ⟨(l' : G) * p, hmL⟩)⁻¹ =
      (α ⟨(x : G), x.2⟩)⁻¹ := by
    rw [hmα]
    apply Subtype.ext
    have e1 : ((α l' : ↥(StatedSL 3 F)) : GL (Fin 3) F) = b := hl'b
    have e2 : ((α x : ↥(StatedSL 3 F)) : GL (Fin 3) F) = g := by rw [hxα]
    show ((α l' : ↥(StatedSL 3 F)) : GL (Fin 3) F) * ((α x : ↥(StatedSL 3 F)) : GL (Fin 3) F) *
      ((α l' : ↥(StatedSL 3 F)) : GL (Fin 3) F)⁻¹ = ((α x : ↥(StatedSL 3 F)) : GL (Fin 3) F)⁻¹
    rw [e1, e2]
    exact hbg
  obtain ⟨s₂, hs₂S, hs₂y, hs₂x⟩ := exists_s2 hq α hα hPS x.2 hxo hxy.symm hxb hmS hmL hmy hmx
  have h2el : ∀ s ∈ Sgp153 T V₁, ∃ k : ℕ, s ^ 2 ^ k = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨y, (x : G), s₁, s₂, hyY, hy3, x.2, hxo, hxy.symm, hxu,
    fun hmem => hxw ((Subgroup.mem_normalizer_iff.mp hmem w).mp hwV), hs₁S, hs₂S, h2el _ hs₁S,
    h2el _ hs₂S, hs₁y, hs₁x, hs₂x, hs₂y⟩

end Main

end Stellmacher.L3YC

end CFSG.Quasithin
