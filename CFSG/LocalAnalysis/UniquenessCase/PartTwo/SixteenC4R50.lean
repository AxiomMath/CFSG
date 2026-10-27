module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R50c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Nonsing
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16TsModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

theorem s16c4_rk_imgTil_le_four {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (F : UFrame V₀ V hV L) {U : Subgroup G}
    (hts : ∀ x : IntMod V hV, x.val ∈ U → F.Sing (mkTil V₀ V hV x)) :
    rk ↥(imgTil V₀ V hV U) ≤ 4 := by
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  let S : AddSubgroup (Fin 4 → F.K) := F.addSub (imgTil V₀ V hV U)
  have hS : ∀ x ∈ S, x ≠ 0 → ∑ i, x i ^ (2 ^ 1 + 1) = 0 := by
    intro x hx _
    have hxU : F.ofVec x ∈ imgTil V₀ V hV U :=
      (F.mem_addSub (imgTil V₀ V hV U) x).1 hx
    obtain ⟨y, hyU, hy⟩ := (mem_imgTil V₀ V hV U (F.ofVec x)).1 hxU
    have hs : F.Sing (mkTil V₀ V hV y) := hts y hyU
    rw [hy] at hs
    simpa using (F.Sing_iff_sum (F.ofVec x)).1 hs
  have hcard := totally_singular_card_le (n := 1) (by norm_num : 1 ≤ 1) hF S hS
  have hcardS : Nat.card S = Nat.card ↥(imgTil V₀ V hV U) :=
    F.card_addSub (imgTil V₀ V hV U)
  have hVtil : IsPGroup 2 (Vtil V₀ V hV) := by
    intro v
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV v
    exact ⟨1, by rw [pow_one, ← map_pow, IntMod.sq_eq_one, map_one]⟩
  have hImg2 : IsPGroup 2 ↥(imgTil V₀ V hV U) := hVtil.to_subgroup (imgTil V₀ V hV U)
  have hcardImg : Nat.card ↥(imgTil V₀ V hV U) = 2 ^ rk ↥(imgTil V₀ V hV U) :=
    card_eq_two_pow_of_isPGroup hImg2
  have h16 : Nat.card ↥(imgTil V₀ V hV U) ≤ 2 ^ 4 := by
    rw [← hcardS]
    simpa using hcard
  rw [hcardImg] at h16
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h16

theorem s16c4_r50_one (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (h4 : Case167_4 D V₀ V hV L)
    (F : UFrame V₀ V hV L) : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hH : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hbc : 4 + (mSub V₀ + 4) ≤ mSub V := by
    have h := F.mSub_V hS
    omega
  refine le_rMV_of_forall_rk_imgTil_le D hH (b := 4) (c := mSub V₀ + 4) hbc ?_
  intro U hUV hU
  change rk ↥(imgTil V₀ V hV U) ≤ 4
  exact s16c4_rk_imgTil_le_four F
    (s16c4_ts_of_not_centralizer_le D h61 hS h4 F hUV hU).1

theorem s16c4_r50_two (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (F : UFrame V₀ V hV L) : (2 : ℕ∞) ≤ deltaInf D.M V := by
  simpa using succ_le_deltaInf_of_mBarGT D hS.setting.hyp16.hyp125 (F.mBarGT_one hS)

theorem s16c4_r50_three (D : Data G) (h61 : UC6.R6_1 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV) (h4 : Case167_4 D ⊥ V hV L)
    (F : UFrame ⊥ V hV L) : (4 : ℕ∞) < rMV D.M V := by
  have hH : Hyp125 D ⊥ V := hS.setting.hyp16.hyp125
  have hbot : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk_bot]
  have h8 : mSub V = 8 := by
    have h := F.mSub_V hS
    rw [hbot] at h
    omega
  have h5 : (5 : ℕ∞) ≤ rMV D.M V := by
    refine le_rMV_of_forall_rk_imgTil_le D hH (b := 3) (c := 5) (by omega) ?_
    intro U hUV hU
    change rk ↥(imgTil ⊥ V hV U) ≤ 3
    have hts := (s16c4_ts_of_not_centralizer_le D h61 hS h4 F hUV hU).1
    have hle4 : rk ↥(imgTil ⊥ V hV U) ≤ 4 := s16c4_rk_imgTil_le_four F hts
    have hne4 : rk ↥(imgTil ⊥ V hV U) ≠ 4 := by
      intro hrk
      exact hU (s16c4_centralizer_le_of_ts_four D h61 hS h4 F hUV hts hrk)
    omega
  exact lt_of_lt_of_le (by norm_num : (4 : ℕ∞) < 5) h5

theorem r16_50_holds (D : Data G) (h61 : UC6.R6_1 D) (hV1 : Case167_4_V1Eq D) : R16_50 D := by
  intro V₀ V L hV hS h4
  obtain ⟨F⟩ := exists_uFrame D h4 (hV1.v1Sub_eq hS h4)
  refine ⟨s16c4_r50_one D h61 hS h4 F, s16c4_r50_two D hS F, ?_⟩
  rintro rfl
  exact s16c4_r50_three D h61 hS h4 F

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
