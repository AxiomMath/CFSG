module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4MS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3 Sec121H9

namespace Sec1214

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ T₀ : Subgroup G} {v : G}
  (c : Setting T L V V₁ V₂ v T₀)
include c

theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (V : Set G) :=
  c.S.ctx.hTL.trans (Sec121Q.normalizer_le_of_hyp121 c.S.ctx.hyp)

theorem le_T₁_of_isMaxElemAbelian (hFF : LemH9FF4) {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) := by
  have hV := c.S.ctx.hVe
  have hcV : IsMulCommutative ↥V := hV.1
  have hVT : V ≤ T := c.S.ctx.V_le_T
  have hTN := c.T_le_normalizer_V
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTN
  have hV₁V : V₁ ≤ V := c.S.ctx.V₁_le
  intro a ha
  refine ⟨hA.1 ha, ?_⟩
  by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
  · exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (by exact_mod_cast hV₁V) (hAC ha))
  have hV2 : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hAs := offenderImages_isFFStarOffender hV hVT hTN ⟨A, ⟨hA, hAC⟩, rfl⟩
  have hr := (rAV_le_one_iff hV2 hAs.isA2).1 (B1_4_1 hV2 hAs)
  have hH9 := h9Hyp_of_hyp121 c.S.ctx.hyp c.S.ctx.hTL hV
  have hAL := hFF _ _ _ _ _ _ hH9 (autI hV A) (autI_mono hV (hA.1.trans c.S.ctx.hTL))
    (isElemAbelian2_autI hV hA.2.1 hAN) hAs.2.1 hr
  have hφ : convI hV ⟨a, hAN ha⟩ ∈ autI hV L := hAL ((mem_autI hV).2 ⟨⟨a, hAN ha⟩, ha, rfl⟩)
  refine Sec121Swap.mem_normalizer_of_conj_mem fun x hx => ?_
  have h1 := hH9.inv₁ hφ (IntMod.mk hV ⟨x, hV₁V hx⟩)
  rw [mem_subI, mem_subI, convI_apply_val] at h1
  exact h1.mp hx

theorem thompsonJ_le (hFF : LemH9FF4) :
    thompsonJ T ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) :=
  iSup₂_le fun _ hA => c.le_T₁_of_isMaxElemAbelian hFF hA

theorem thompsonJ_T₁ (hFF : LemH9FF4) :
    thompsonJ (T ⊓ Subgroup.normalizer (V₁ : Set G)) = thompsonJ T :=
  B6.thompsonJ_eq_of_le (c.thompsonJ_le hFF) inf_le_left

theorem T₀_le_normalizer_thompsonJ (hFF : LemH9FF4) :
    T₀ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  rw [← c.thompsonJ_T₁ hFF]
  exact c.hT₀N.trans (normalizer_le_normalizer_thompsonJ _)

theorem not_normalizer_thompsonJ_le (hFF : LemH9FF4) :
    ¬ Subgroup.normalizer (thompsonJ T : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  fun h => c.hT₀M ((c.T₀_le_normalizer_thompsonJ hFF).trans h)

theorem thompsonJ_ne_bot : thompsonJ T ≠ ⊥ := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
  intro hb
  have hA₀1 : A₀ = ⊥ := le_bot_iff.mp (hb ▸ B6.le_thompsonJ hA₀)
  have h1 := hA₀.2.2 V c.S.ctx.V_le_T c.S.ctx.hVe
  rw [hA₀1, Subgroup.card_bot] at h1
  have hV1 : V = ⊥ := Subgroup.eq_bot_of_card_le V h1
  exact Sec121Thm.ne_bot_of_hyp121 c.S.ctx.hyp hV1

theorem not_thompsonJ_le_Q (hFF : LemH9FF4) :
    ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  intro hJQ
  have hJ : thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) = thompsonJ T :=
    B6.thompsonJ_eq_of_le hJQ inf_le_left
  have huniq := Sec1215.isUniqueM_of_hyp121 c.h331 c.S.ctx.hyp c.S.ctx.hTL
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) :=
    c.S.ctx.hyp.sylow.1.to_le (B6.thompsonJ_le T)
  obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge ⟨thompsonJ T, c.thompsonJ_ne_bot, hJ2, rfl⟩
  have hNQ : Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (thompsonJ T : Set G) :=
    hJ ▸ normalizer_le_normalizer_thompsonJ _
  have hM : M'' = Subgroup.normalizer (L : Set G) := huniq.2 M'' ⟨hM'', hNQ.trans hle⟩
  exact c.not_normalizer_thompsonJ_le hFF (hM ▸ hle)

end Setting

end Sec1214

end CFSG.Quasithin.H13
