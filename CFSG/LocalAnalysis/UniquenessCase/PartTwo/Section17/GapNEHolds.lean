module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSix
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.GapNE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem calNIn_eq_inf_of_min (D : Data G) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (h66 : UC6.R6_6 D) {H₀ : Subgroup G} (hmin : Hyp124Min D H₀) :
    calNIn H₀ D.T = {H₀ ⊓ D.M} := by
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).1
  have hT : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hTH : D.T < H₀ := lt_of_le_of_ne hmin.1.1 fun h => hmin.1.2.1 (h ▸ hTM)
  have hlt : H₀ ⊓ D.M < H₀ := lt_of_le_of_ne inf_le_left fun h => hmin.1.2.1 (inf_eq_left.1 h)
  by_cases hsp : IsStronglyPEmbedded 3 D.M
  · have hnot : ¬ F12.HasCompFactor H₀ IsCalL1 := by
      rw [TwelveSix.hasCompFactor_calL1_iff]
      exact hmin.2.1.1
    have hP : ∀ X : Subgroup G, ¬ F12.HasCompFactor X IsCalL1 →
        CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M X := by
      intro X hX
      rw [TwelveSix.hasCompFactor_calL1_iff] at hX
      exact ⟨hX, fun h => absurd hsp h⟩
    have hLle := TwelveSix.lGen_le_inf D hmin hP
    have hne : H₀ ≠ lGen IsCalL1 H₀ D.T := (lt_of_le_of_lt hLle hlt).ne'
    obtain ⟨hcalN, -⟩ :=
      h5_13 G H₀ D.T (TwelveSix.isKGroup_of_mem_hSet D hmin.1) hT hTH
        (TwelveSix.pRank_three_le_one D h66 hmin.1 hsp) hnot hne
    exact TwelveSix.calNIn_eq_inf D hmin.1.2.1 hmin.1.1 hcalN hLle
  · have hnot : ¬ F12.HasCompFactor H₀ IsCalL0 := by
      rw [TwelveSix.hasCompFactor_calL0_iff]
      exact hmin.2.1.2 hsp
    have hP : ∀ X : Subgroup G, ¬ F12.HasCompFactor X IsCalL0 →
        CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M X := by
      intro X hX
      rw [TwelveSix.hasCompFactor_calL0_iff] at hX
      exact ⟨fun ⟨L, _, hL, hA⟩ =>
        hX ⟨L, inferInstance, hL, CFSG.LocalAnalysis.RankThreeUC.listA_le_listB L hA⟩,
        fun _ => hX⟩
    have hLle := TwelveSix.lGen_le_inf D hmin hP
    have hne : H₀ ≠ lGen IsCalL0 H₀ D.T := (lt_of_le_of_lt hLle hlt).ne'
    have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p H₀ ≤ 3 ∨ CFSG.Open.pRank p (lGen IsCalL0 H₀ D.T) ≤ 1 := by
      intro p hp hp2
      by_cases h3 : CFSG.Open.pRank p H₀ ≤ 3
      · exact Or.inl h3
      · exact Or.inr ((CFSG.SectionRank.pRank_mono hp.one_lt hLle).trans
          (TwelveSix.pRank_inf_le_one D h66 hmin.1 hp hp2 (not_le.1 h3)))
    obtain ⟨⟨hcalN, -⟩, -⟩ :=
      h5_11 G H₀ D.T (TwelveSix.isKGroup_of_mem_hSet D hmin.1) hT hTH hnot hne hrank
    exact TwelveSix.calNIn_eq_inf D hmin.1.2.1 hmin.1.1 hcalN hLle

theorem isCalH0_of_min (D : Data G) {V₀ V H₀ : Subgroup G} (hV : Hyp125 D V₀ V)
    (hmin : Hyp124Min D H₀) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (h66 : UC6.R6_6 D)
    (h861 : W3Lem86_1 G) (hm : 2 < mSub V₀) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) : IsCalH0 V₀ H₀ := by
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
    omega
  obtain ⟨hV0, hCU, -⟩ : InCalV0 D.M V₀ V ∧ CentralizersUnique D.M D.T ∧
      ∀ W : Subgroup G, ¬ InCalW D.M D.T W := by
    rcases hV.1 with ⟨-, hbot⟩ | h
    · exact absurd hbot hV0ne
    · exact h
  have hVel : IsElemAbelian 2 V₀ := hV0.1.2.2.2
  have hV0T : V₀ ≤ D.T := IsSylowIn.le_of_normal (TwelveShort.isSylowIn_of_le D D.sylowM.le)
    hV0.1.2.1 (Subgroup.normal_subgroupOf_iff_le_normalizer hV0.1.2.1 |>.2 hV0.1.2.2.1)
    (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hVel)
  have hVcard : Nat.card V₀ = 2 ^ mSub V₀ := by
    rw [mSub]
    exact CFSG.Quasithin.card_eq_two_pow_of_isPGroup
      (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hVel)
  have hW : E3.wClos V₀ 0 D.T ≠ V₀ :=
    TwelveFourteen.wClos_zero_ne_self hTim hcat D hV0.1 hV0.2.2.2.1 (by
      rw [hVcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hV7 : Hyp7 V₀ := by
    refine ⟨hVel, ?_, hV0.2.2.2.1⟩
    rw [hVcard]
    have h2m : 2 < mSub V₀ := by omega
    have : 2 ^ 2 < 2 ^ mSub V₀ := Nat.pow_lt_pow_right (by norm_num) h2m
    omega
  have hH := hmin.1
  have hNM : Subgroup.normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV0.1
  have hTH : D.T ≤ H₀ ⊓ Subgroup.normalizer (V₀ : Set G) :=
    le_inf hH.1 (hNM ▸ D.sylowM.le)
  have hT : IsSylowIn 2 D.T (H₀ ⊓ Subgroup.normalizer (V₀ : Set G)) :=
    TwelveShort.isSylowIn_of_le D hTH
  have hcalH : IsCalH V₀ H₀ := by
    refine ⟨hV0T.trans hH.1, ?_, ?_⟩
    · exact hH.2.2
    · have hS := TwelveShort.isSylowIn_of_le D hH.1
      have hmul := Subgroup.relIndex_mul_relIndex D.T
        (H₀ ⊓ Subgroup.normalizer (V₀ : Set G)) H₀ hTH inf_le_left
      have hodd : ¬ 2 ∣ D.T.relIndex H₀ := hS.2.2
      rw [← hmul] at hodd
      exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => hodd (Dvd.dvd.mul_left h _))
  have hC : CentralizersInM V₀ H₀ D.T := by
    intro z hz hzc hz1
    rw [hNM]
    exact inf_le_right.trans (hCU z hz hzc hz1).1
  refine ⟨hcalH, ?_⟩
  by_contra hO
  have h86 := (h861 V₀ H₀ D.T hV7 hcalH (fun h0 => hO h0.2) hT hW (Or.inl hC)).1
  set W : Subgroup G := E3.wClos V₀ 0 D.T with hWdef
  have hTN : D.T ≤ H₀ ⊓ normalizer (W : Set G) :=
    le_inf hH.1 (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos D.T))
  by_cases hNH : H₀ ⊓ normalizer (W : Set G) = H₀
  ·
    have hWT : W ≤ D.T := E3.wClos_le 0 D.T
    have hWH : W ≤ H₀ := hWT.trans hH.1
    have hHW : H₀ ≤ normalizer (W : Set G) := by
      rw [← hNH]
      exact inf_le_right
    have hT2 : IsPGroup 2 D.T := hT.isPGroup
    have hW2 : W ≤ pCoreOf 2 H₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWH hHW (hT2.to_le hWT)
    have hV0W : V₀ ≤ W := E3.le_wClos ⟨hV0T, 1, (conjSubgroup_one V₀).symm.le, by
      rw [conjSubgroup_one]
      exact E3.mQuot_self V₀⟩
    exact hO (hV0W.trans hW2)
  ·
    have hlt : H₀ ⊓ normalizer (W : Set G) < H₀ := lt_of_le_of_ne inf_le_left hNH
    obtain ⟨X, hX, hle⟩ := exists_mem_calNIn_of_lt hTN hlt
    rw [calNIn_eq_inf_of_min D h5_11 h5_13 h66 hmin, Set.mem_singleton_iff] at hX
    subst hX
    apply hH.2.1
    calc H₀ = (H₀ ⊓ normalizer (V₀ : Set G)) ⊔ (H₀ ⊓ normalizer (W : Set G)) := h86
      _ ≤ D.M := sup_le (hNM ▸ inf_le_right) (hle.trans inf_le_right)

theorem gap17_26_NE_holds (D : Data G) (V₀ V H₀ : Subgroup G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (h66 : UC6.R6_6 D) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G) :
    Gap17_26_NE D V₀ V H₀ :=
  fun hV hmin hm hnot =>
    absurd (isCalH0_of_min D hV hmin h5_11 h5_13 h66 h861 (by omega) hTim hcat) hnot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
