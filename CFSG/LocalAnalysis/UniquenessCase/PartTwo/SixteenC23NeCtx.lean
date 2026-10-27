module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23ne_ctx_of_case (D : Data G) (h119 : F11.R119 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L) (hne : V₀ ≠ ⊥) :
    ∃ (x : G) (K₁ K₂ : Subgroup G), C23NeCtx D V₀ V L hV x K₁ K₂ := by
  have h151 := hS.setting.hyp151
  have hP := h151.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨x, hx, hxn⟩ := c23_exists_mem_not_nBar D h151 hV hc.2.2.1
  have hL3 : IsL3 ↥(barSub V₀ V hV L) 1 := hc.1
  have hnat := c23ne_binaryNatural D.M hV hne hc.2.1
  have hcore := c23ne_core_of_case2 h1217 h151 hV hc.2.2.1 hL3 hnat hx hxn
  obtain ⟨e⟩ := c23_barSub_conj_equiv (V₀ := V₀) hV (hMs hx) L
  have hL3' : IsL3 ↥(barSub V₀ V hV (conjSubgroup L x)) 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL3
  have hinf := c23_core_inf_A_eq_bot hcore
  obtain ⟨K₁, K₂, hK₁, hK₂, hne₁₂, hb₁, hb₂, hn₁, hn₂, hperm⟩ :=
    c23ne_lift_factors D h119 hV hP.le_normalizer hP.le_normalizer₀
      (Hyp125.hyp11 h127 h151.hyp125) (barSub_mono V₀ V hV h151.le)
      (c23_barSub_conjSubgroup_le_Mbar D h151 hV hx)
      (fun a ha b hb => c23_core_commute hcore ha hb) hinf hL3 hL3'
      (c23_perm_barSub D h151 hV hc.2.2.1 hx hxn)
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal hK₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal hK₂.1
  have hLa : IsL3 ↥(barSub V₀ V hV K₁) 1 := by rw [hb₁]; exact hL3
  have hLb : IsL3 ↥(barSub V₀ V hV K₂) 1 := by rw [hb₂]; exact hL3'
  have hinf' : barSub V₀ V hV K₁ ⊓ barSub V₀ V hV K₂ = ⊥ := by rw [hb₁, hb₂]; exact hinf
  have hker := c23ne_ker_eq hV hMs hK₁ hK₂ hn₁ hn₂ hLa hLb hinf'
  have hV₀e := hP.elemAbelian₀
  have hsmall : mSub V₀ ≤ 2 := hS.setting.hyp16.small
  refine ⟨x, K₁, K₂, ⟨hx, hxn, hcore, hK₁, hK₂, hne₁₂, hb₁, hb₂, ?_, ?_, hn₁, hn₂,
    hperm, ?_, hker.1, hker.2⟩⟩
  · exact (c23ne_bar2_of_calC hV hMs hK₁M hK₁.2.2 hLa).1
  · exact (c23ne_bar2_of_calC hV hMs hK₂M hK₂.2.2 hLb).1
  · exact sup_le
      (c23ne_centralizes_V₀ hK₁.2.1 hV₀e hsmall (hK₁M.trans hP.le_normalizer₀))
      (c23ne_centralizes_V₀ hK₂.2.1 hV₀e hsmall (hK₂M.trans hP.le_normalizer₀))

theorem c23ne_hyp141 (D : Data G) (hx : DataExt D) (h115 : F11.R115 D) (h127 : R127 D)
    (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_2 D V₀ V hV L) {x : G} {K₁ K₂ X : Subgroup G}
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hXsyl : CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂)) (hperm : Permutes X D.T) :
    Hyp141 D K₁ K₂ X :=
  ⟨hc.2.2.2, c23_evenRank_eq_three D hx h115 h127 h1217 hS (Or.inl hc), hctx.mem₁, hctx.mem₂,
    hctx.ne, hctx.shape₁, hctx.shape₂, hXsyl, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
