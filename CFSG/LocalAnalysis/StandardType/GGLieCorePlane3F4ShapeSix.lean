module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.F4LowRankShapes
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4
  CFSG.SeitzReduction.F4Pilot CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes
open CFSG.Open (StatedLieTag)

private theorem l10lF1_single_shape
    (j : Fin Tag.F4.rank) :
    compRank ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) = 1 ∧
      ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).ncard = 2 := by
  have hpair : kacF4.rootsOf (({some j} : Finset (Option (Fin Tag.F4.rank))) : Set _) =
      ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
    rw [Finset.coe_singleton, rootsOf_singleton kacF4 (some j)]
    simp [KacData.extRoot]
  have hnone : ∃ x, x ∉ ({some j} : Finset (Option (Fin Tag.F4.rank))) := ⟨none, by simp⟩
  constructor
  · rw [← hpair, compRank_rootsOf kacF4 facts_F4 (C := {some j}) hnone]
    simp
  · rw [← hpair, Finset.coe_singleton]
    exact ncard_rootsOf_singleton kacF4 (some j)

private theorem l10lF1_parabolic_shape
    (C : Finset (Option (Fin Tag.F4.rank))) (J : Set (Fin Tag.F4.rank)) (r n : ℕ)
    (hnone : none ∉ C) (hCJ : ∀ j, some j ∈ C ↔ j ∈ J)
    (hcard : C.card = r) (hn : kacCount Tag.F4 kacF4.θ C = n) :
    compRank (parabolicRoots Tag.F4 J) = r ∧ (parabolicRoots Tag.F4 J).ncard = n := by
  have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 J :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 hnone hCJ
  constructor
  · rw [← hroots, compRank_rootsOf kacF4 facts_F4 ⟨none, hnone⟩, hcard]
  · rw [← hroots, ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩, hn]

theorem ggLieF4Plane_shape_six
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂)) :
    GGLieF4PlaneShape (componentRoots (jointChar a₁ a₂) i) ∨
      (compRank (componentRoots (jointChar a₁ a₂) i) = 3 ∧
        (componentRoots (jointChar a₁ a₂) i).ncard = 18) := by
  have ha : ∀ j, a₁ j ^ 3 = 1 := pow_eq_one_of_rootDiagUnit_pow (a := a₁) h.pow₁
  have hd : ∀ j, a₂ j ^ 3 = 1 := pow_eq_one_of_rootDiagUnit_pow (a := a₂) h.pow₂
  have hne : rootDiagUnit Tag.F4 a₁ ≠ 1 ∨ rootDiagUnit Tag.F4 a₂ ≠ 1 := by
    by_contra hc
    have hb₁ : rootDiagUnit Tag.F4 a₁ = 1 := by
      by_contra hb; exact hc (Or.inl hb)
    have hb₂ : rootDiagUnit Tag.F4 a₂ = 1 := by
      by_contra hb; exact hc (Or.inr hb)
    have hbot : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 L)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr hb₁
      · exact Subgroup.mem_bot.mpr hb₂
    have hcard := h.card
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨w, hw⟩ :=
    CFSG.StandardType.F4ExplicitPos.JointShapes.f4_joint_component_six_shape
      (p := 3) (by norm_num) (by norm_num) a₁ a₂ ha hd hne i
  rcases hw with ⟨j, hj⟩ | hlong | hshort | hb2 | hB3 | hC3
  · refine Or.inl (Or.inl ?_)
    obtain ⟨hr, hn⟩ := l10lF1_single_shape j
    exact ⟨by rw [hj, compRank_image]; exact hr, by rw [hj, ncard_image_smul]; exact hn⟩
  · refine Or.inl (Or.inr (Or.inl ?_))
    obtain ⟨hr, hn⟩ := l10lF1_parabolic_shape {some 0, some 1} f4LongSupport 2 6
      (by decide) (by intro j; rw [mem_f4LongSupport]; revert j; decide +kernel) (by decide)
      (by rw [show kacF4.θ = ![2, 3, 4, 2] from rfl]; decide +kernel)
    exact ⟨by rw [hlong, compRank_image]; exact hr, by rw [hlong, ncard_image_smul]; exact hn⟩
  · refine Or.inl (Or.inr (Or.inl ?_))
    obtain ⟨hr, hn⟩ := l10lF1_parabolic_shape {some 2, some 3} f4ShortSupport 2 6
      (by decide) (by intro j; rw [mem_f4ShortSupport]; revert j; decide +kernel) (by decide)
      (by rw [show kacF4.θ = ![2, 3, 4, 2] from rfl]; decide +kernel)
    exact ⟨by rw [hshort, compRank_image]; exact hr, by rw [hshort, ncard_image_smul]; exact hn⟩
  · refine Or.inl (Or.inr (Or.inr ?_))
    have hb2' : compRank b2LeviRoots = 2 ∧ b2LeviRoots.ncard = 8 := by
      rw [b2LeviRoots]
      exact l10lF1_parabolic_shape {some 1, some 2} nodesTU 2 8
        (by decide) (by intro j; rw [mem_nodesTU]; revert j; decide +kernel) (by decide)
        (by rw [show kacF4.θ = ![2, 3, 4, 2] from rfl]; decide +kernel)
    exact ⟨by rw [hb2, compRank_image]; exact hb2'.1,
      by rw [hb2, ncard_image_smul]; exact hb2'.2⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hB3, compRank_image,
        CFSG.StandardType.F4ExplicitPos.SelectedLiteral.compRank_parabolicRoots_f4LeviB3]
    · rw [hB3, ncard_image_smul,
        CFSG.StandardType.F4ExplicitPos.SelectedLiteral.ncard_parabolicRoots_f4LeviB3]
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hC3, compRank_image,
        CFSG.StandardType.F4ExplicitPos.SelectedLiteral.compRank_parabolicRoots_f4LeviC3]
    · rw [hC3, ncard_image_smul,
        CFSG.StandardType.F4ExplicitPos.SelectedLiteral.ncard_parabolicRoots_f4LeviC3]

end CFSG.StandardType.LieCore
