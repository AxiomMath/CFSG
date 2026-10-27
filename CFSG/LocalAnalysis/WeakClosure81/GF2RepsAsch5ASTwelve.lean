module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixLocal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem inFSqAS_of_not_sp (D : Data G) (h5_11 : Asch5_11AS) (h66 : UC6.R6_6 D) {H₀ : Subgroup G}
    (hmin : Hyp124Min D H₀) (hsp : ¬ IsStronglyPEmbedded 3 D.M) : InFSqAS 1 H₀ ∨ InFSqAS 2 H₀ := by
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).1
  have hT : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hTH : D.T < H₀ := lt_of_le_of_ne hmin.1.1 fun h => hmin.1.2.1 (h ▸ hTM)
  have hnot : ¬ F12.HasCompFactor H₀ IsCalL0 := by
    rw [TwelveSix.hasCompFactor_calL0_iff]
    exact hmin.2.1.2 hsp
  have hP : ∀ X : Subgroup G, ¬ F12.HasCompFactor X IsCalL0 →
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M X := by
    intro X hX
    rw [TwelveSix.hasCompFactor_calL0_iff] at hX
    exact ⟨fun ⟨L, _, hL, hA⟩ =>
      hX ⟨L, inferInstance, hL, CFSG.LocalAnalysis.RankThreeUC.listA_le_listB L hA⟩, fun _ => hX⟩
  have hLle := TwelveSix.lGen_le_inf D hmin hP
  have hlt : H₀ ⊓ D.M < H₀ := lt_of_le_of_ne inf_le_left fun h => hmin.1.2.1 (inf_eq_left.1 h)
  have hne : H₀ ≠ lGen IsCalL0 H₀ D.T := (lt_of_le_of_lt hLle hlt).ne'
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p H₀ ≤ 3 ∨ CFSG.Open.pRank p (lGen IsCalL0 H₀ D.T) ≤ 1 := by
    intro p hp hp2
    by_cases h3 : CFSG.Open.pRank p H₀ ≤ 3
    · exact Or.inl h3
    · exact Or.inr ((CFSG.SectionRank.pRank_mono hp.one_lt hLle).trans
        (TwelveSix.pRank_inf_le_one D h66 hmin.1 hp hp2 (not_le.1 h3)))
  obtain ⟨-, h | ⟨h, -⟩⟩ :=
    h5_11 G H₀ D.T (TwelveSix.isKGroup_of_mem_hSet D hmin.1) hT hTH hnot hne hrank
  · exact Or.inl h
  · exact Or.inr h

theorem inFSqAS_of_sp (D : Data G) (h5_13 : Asch5_13AS)
    (h66 : UC6.R6_6 D) {H₀ : Subgroup G} (hmin : Hyp124Min D H₀)
    (hsp : IsStronglyPEmbedded 3 D.M) : InFSqAS 1 H₀ := by
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).1
  have hT : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hTH : D.T < H₀ := lt_of_le_of_ne hmin.1.1 fun h => hmin.1.2.1 (h ▸ hTM)
  have hnot : ¬ F12.HasCompFactor H₀ IsCalL1 := by
    rw [TwelveSix.hasCompFactor_calL1_iff]
    exact hmin.2.1.1
  have hP : ∀ X : Subgroup G, ¬ F12.HasCompFactor X IsCalL1 →
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M X := by
    intro X hX
    rw [TwelveSix.hasCompFactor_calL1_iff] at hX
    exact ⟨hX, fun h => absurd hsp h⟩
  have hLle := TwelveSix.lGen_le_inf D hmin hP
  have hlt : H₀ ⊓ D.M < H₀ := lt_of_le_of_ne inf_le_left fun h => hmin.1.2.1 (inf_eq_left.1 h)
  have hne : H₀ ≠ lGen IsCalL1 H₀ D.T := (lt_of_le_of_lt hLle hlt).ne'
  obtain ⟨hcalN, h | ⟨n, hn, hshape⟩⟩ :=
    h5_13 G H₀ D.T (TwelveSix.isKGroup_of_mem_hSet D hmin.1) hT hTH
      (TwelveSix.pRank_three_le_one D h66 hmin.1 hsp) hnot hne
  · exact h
  · exact absurd hshape (TwelveSix.not_fStar_shape hsp
      (TwelveSix.calNIn_eq_inf D hmin.1.2.1 hmin.1.1 hcalN hLle) hT hTM hmin.1.2.1 n hn)

theorem twelve_six_AS (D : Data G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (h66 : UC6.R6_6 D) {H₀ : Subgroup G} (hmin : Hyp124Min D H₀) :
    E1.InE D.k H₀ := by
  by_cases hsp : IsStronglyPEmbedded 3 D.M
  · have hk : D.k = 1 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      rw [if_pos hsp]
    rw [hk]
    exact inE_of_inFSqAS (inFSqAS_of_sp D h5_13 h66 hmin hsp)
  · have hk : D.k = 2 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      rw [if_neg hsp]
    rw [hk]
    rcases inFSqAS_of_not_sp D h5_11 h66 hmin hsp with h | h
    · exact (inE_of_inFSqAS h).mono (by norm_num)
    · exact inE_of_inFSqAS h

theorem r126_of_twelve_six_AS (D : Data G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (h66 : UC6.R6_6 D) : R126 D := by
  exact fun _ hmin => twelve_six_AS D h5_11 h5_13 h66 hmin

end CFSG.LocalAnalysis.WeakClosure81
