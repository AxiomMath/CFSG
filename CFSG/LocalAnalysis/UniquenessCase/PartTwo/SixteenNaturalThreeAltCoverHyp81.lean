module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCoverParabolic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.L34ComponentCoverFacts
public import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_exists_alt_ten_eleven_cover_hyp81
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 1)
    {n : ℕ} (hn : n = 10 ∨ n = 11)
    (hAlt : UC22.IsAlt ↥(lBar V₀ V hV L) n) :
    ∃ (Y : Subgroup G) (hYM : Y ≤ D.M),
      Y ∈ calC D.M ∧
      (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = lBar V₀ V hV L ∧
      ¬ 3 ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) ∧
      ∃ e : Bar2 Y ≃* ↥(lBar V₀ V hV L),
        (∀ y : ↥Y,
          (e (QuotientGroup.mk y) : MulAut (Vtil V₀ V hV)) =
            actTil V₀ V hV
              ⟨(y : G), c.m_le_stabTil (hYM y.2)⟩) ∧
        Nonempty ((Bar2 Y ⧸ Subgroup.center (Bar2 Y)) ≃*
          ↥(lBar V₀ V hV L)) ∧
        Subgroup.center (Bar2 Y) = ⊥ ∧
        UC22.IsAlt (Bar2 Y) n ∧
        UC22.IsAlt (Bar2 Y ⧸ Subgroup.center (Bar2 Y)) n ∧
        CFSG.Open.pRank 3 Y = 3 ∧
        CFSG.LocalAnalysis.UniquenessCase.UC22.F08.Hyp81 D.M Y ∧
        CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo Y ∧
        CFSG.Yardstones.Mf4cdcdf2e013.Hyp81 D.M Y := by
  classical
  let B : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn8 : 8 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hsimpleB : IsSimpleGroup ↥B :=
    s16c167_cfg2_simple_alt hn5 (by simpa [B] using hAlt)
  have hnorm : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (B : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [B] using lBar_conj_eq_of_s15_eq_one hs hg
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥B) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hqQ ⟨eQ⟩
    have hperfQ : Group.IsPerfect Q := ⟨hqQ.1⟩
    have hZ : Nat.card (Subgroup.center Q) ≤ 2 :=
      @CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt Q _ _ hperfQ n hn8
        (eQ.trans hAlt.some)
    intro h3
    have h3le : 3 ≤ Nat.card (Subgroup.center Q) := Nat.le_of_dvd Nat.card_pos h3
    omega
  obtain ⟨Y, hYmem, hYM, hYnorm, hYbar, hY3⟩ :=
    s168e3_exists_normal_cover_three_free c hcomp hsimpleB hnorm hcover
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 h125
  have hCcomp : CFSG.IsComponent (UC22.barImage D.M Y) :=
    UC22.uc22p22l_barImage_isComponent hYmem
  have hmap : (UC22.barImage D.M Y).map ψ = B := by
    simpa [B] using barImage_map_eq_of_mem_calC h125 hYmem hYbar ψ hψ
  obtain ⟨eBar, heBar⟩ := UC22.uc22p22l_barImage_equiv hYmem
  obtain ⟨eCZ, heCZ⟩ :=
    exists_quotient_center_equiv_of_map_eq ψ hCcomp hmap hsimpleB
  have hcenterImage : (Subgroup.center (Bar2 Y)).map
      (eBar : Bar2 Y →* ↥(UC22.barImage D.M Y)) =
      Subgroup.center (UC22.barImage D.M Y) := by
    simp
  let eYQ : (Bar2 Y ⧸ Subgroup.center (Bar2 Y)) ≃* ↥B :=
    (QuotientGroup.congr (Subgroup.center (Bar2 Y))
      (Subgroup.center (UC22.barImage D.M Y)) eBar hcenterImage).trans eCZ
  have heYQ_mk : ∀ x : Bar2 Y,
      (eYQ (QuotientGroup.mk x) : MulAut (Vtil V₀ V hV)) = ψ (eBar x) := by
    intro x
    calc
      (eYQ (QuotientGroup.mk x) : MulAut (Vtil V₀ V hV)) =
          (eCZ (QuotientGroup.mk (eBar x)) : MulAut (Vtil V₀ V hV)) := by
            dsimp only [eYQ]
            rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
      _ = ψ (eBar x) := congrArg Subtype.val (heCZ (eBar x))
  have hperfY : Group.IsPerfect (Bar2 Y) := ⟨hYmem.2.2.1⟩
  have hZle2 : Nat.card (Subgroup.center (Bar2 Y)) ≤ 2 :=
    @CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt (Bar2 Y) _ _ hperfY n hn8
      (eYQ.trans hAlt.some)
  have hoddZ : Odd (Nat.card (Subgroup.center (Bar2 Y))) :=
    (s15_Three_bar2_facts hYmem).2
  have hcenter : Subgroup.center (Bar2 Y) = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rcases hoddZ with ⟨k, hk⟩
    omega
  let e : Bar2 Y ≃* ↥B :=
    ((QuotientGroup.quotientBot (G := Bar2 Y)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (G := Bar2 Y) hcenter.symm)).trans eYQ
  have he_apply : ∀ y : ↥Y,
      (e (QuotientGroup.mk y) : MulAut (Vtil V₀ V hV)) =
        actTil V₀ V hV
          ⟨(y : G), c.m_le_stabTil (hYM y.2)⟩ := by
    intro y
    calc
      (e (QuotientGroup.mk y) : MulAut (Vtil V₀ V hV)) =
          (eYQ (QuotientGroup.mk (QuotientGroup.mk y)) :
            MulAut (Vtil V₀ V hV)) := by
            simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientBot_symm_apply,
              QuotientGroup.quotientMulEquivOfEq_mk]
      _ = ψ (eBar (QuotientGroup.mk y)) := heYQ_mk (QuotientGroup.mk y)
      _ = actTil V₀ V hV ⟨(y : G), c.m_le_stabTil (hYM y.2)⟩ := by
            rw [show (eBar (QuotientGroup.mk y) : Bar2 D.M) =
              QuotientGroup.mk (Subgroup.inclusion hYM y) from heBar y]
            exact hψ ⟨(y : G), hYM y.2⟩
  have hrank_bar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 Y)) = CFSG.Open.pRank 3 Y :=
    UC22.pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)
  have hrank_B : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 Y)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥B) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
  have hrank_alt : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥B) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) hAlt.some]
    exact CFSG.SectionRank.three_le_pRank_alternating (by omega)
  have hrank_ge3 : 3 ≤ CFSG.Open.pRank 3 Y := by
    rw [← hrank_bar, hrank_B]
    exact hrank_alt
  have hrank_le3 : CFSG.Open.pRank 3 Y ≤ 3 := by
    have hM := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hYM
    have hG := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank
      3 Nat.prime_three (by norm_num) D.M D.maxLocal.1
    rw [c.std.h3] at hG
    exact hM.trans hG
  have hrank3 : CFSG.Open.pRank 3 Y = 3 := le_antisymm hrank_le3 hrank_ge3
  have hF08 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.Hyp81 D.M Y :=
    ⟨hYmem.1, hYmem.2.1, by omega, Or.inl (s15_Three_qs_of_open hYmem.2.2)⟩
  have hY81 : CFSG.Yardstones.Mf4cdcdf2e013.Hyp81 D.M Y :=
    UC22.hyp81_of_f08 hF08
  have hQ : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo Y :=
    ⟨inferInstance, hYmem.2.2⟩
  refine ⟨Y, hYM, hYmem, hYnorm, hYbar, hY3, e, he_apply, ⟨eYQ⟩,
    hcenter, ⟨e.trans hAlt.some⟩, ⟨eYQ.trans hAlt.some⟩, hrank3, hF08, hQ, hY81⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
