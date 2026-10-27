module

public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Basic
public import CFSG.LocalAnalysis.StandardType.GGTorsionBC
public import CFSG.LocalAnalysis.StandardType.GGTorsionOrth
public import CFSG.LocalAnalysis.StandardType.GGTorsionBCDClass
import CFSG.LocalAnalysis.StandardType.GGTorsionE67Linear
import CFSG.LocalAnalysis.StandardType.GGTorsionPSpComp
import CFSG.LocalAnalysis.StandardType.GGTorsionPOmegaComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionE67BCD

private theorem e67bcd_center_eq_bot {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem ggTorsionKnownOverTagsE67_typeBC :
    GGTorsionKnownOverTags (fun lab => lab.tag = .B ∨ lab.tag = .C)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .B ∨ lab.tag = .C := by
    obtain ⟨R, _, I, F, -, -, θ, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htag
  rcases htag with rfl | rfl
  all_goals
    obtain ⟨hn, hr1, hr2⟩ := hlab
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, _, _, hK, hs, hna, θ, -, hI⟩ := hraw
    have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
    have hJ' := ggTorsion_isComponentOf_image θ hcomp
    obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
    have hZ := e67bcd_center_eq_bot hs hna
    have key := ggTorsion_psp_components (by omega) hn hK hZ hp hp2 hδp' hI hJ'
    refine ggTorsion_not_markingE67_of_classical ?_ hJ
    rcases key with ⟨t', n', f', hL⟩ | h360
    · exact Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩
    · exact Or.inr (by rw [Nat.card_congr e₂.toEquiv]; exact h360)

theorem ggTorsionKnownOverTagsE67_typeD :
    GGTorsionKnownOverTags (fun lab => lab.tag = .D)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hmark
  have htag : lab.tag = .D := by
    obtain ⟨R, _, I, F, -, -, θ, ⟨⟨hP, -⟩, -⟩⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  obtain rfl : t = .D := htag
  obtain ⟨hn, hr⟩ := hlab
  have hn1 : 1 ≤ n := hn
  have hr' : 3 ≤ r := hr
  by_cases hr3 : r = 3
  · subst hr3
    refine ggTorsionKnownOverTagsE67_typeA p X hX δ J
      ⟨hp, hp2, hδp, hδ1, hcomp, hXc, ⟨.A, 3, n⟩,
        ⟨hn1, by norm_num, fun h => absurd h (by norm_num)⟩, ?_⟩ hJ
    have h' : LargeEvenRawDatum (⟨.D, 3, n⟩ : LargeEvenLabel)
        (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : X ⧸ Subgroup.center X ≃* R,
            (⟨.A, 3, n⟩ : LargeEvenLabel).tag = .A ∧ ggInducedAut θ δ ∈ I) := by
      refine largeEvenRawDatum_mono ?_ hraw
      rintro R _ I F ⟨hs, hna, θ, ⟨-, hI⟩, -⟩
      exact ⟨hs, hna, θ, rfl, hI⟩
    exact h'
  · dsimp only [LargeEvenRawDatumLegacy] at hraw
    rw [if_neg hr3] at hraw
    obtain ⟨K, _, _, hK, hs, hna, θ, ⟨-, hI⟩, hM⟩ := hraw
    have hM' : CFSG.Open.StatedClassicalModel
        (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) .POmegaPlus r 2 n := by
      have h0 := hM
      dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h0
      rw [if_neg hr3, if_neg hr3] at h0
      exact h0.statedClassicalModel_of_ne_zero (by omega)
    have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
    have hJ' := ggTorsion_isComponentOf_image θ hcomp
    obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
    obtain ⟨t', n', f', hL⟩ := ggTorsion_pomega_components (Or.inl rfl) hM'
      (e67bcd_center_eq_bot hs hna) hp hp2 hδp' hI hJ'
    exact ggTorsion_not_markingE67_of_classical
      (Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩) hJ

theorem ggTorsionKnownOverTagsE67_typeTwD :
    GGTorsionKnownOverTags (fun lab => lab.tag = .twD)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hmark
  have htag : lab.tag = .twD := by
    obtain ⟨R, _, I, F, -, -, θ, ⟨⟨hP, -⟩, -⟩⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  obtain rfl : t = .twD := htag
  obtain ⟨hn, hr⟩ := hlab
  have hn1 : 1 ≤ n := hn
  have hr' : 2 ≤ r := hr
  by_cases hr2' : r = 2
  · subst hr2'
    refine ggTorsionKnownOverTagsE67_typeA p X hX δ J
      ⟨hp, hp2, hδp, hδ1, hcomp, hXc, ⟨.A, 1, 2 * n⟩,
        ⟨show 1 ≤ 2 * n by omega, le_rfl, fun _ => show 2 ≤ 2 * n by omega⟩, ?_⟩ hJ
    have h' : LargeEvenRawDatum (⟨.twD, 2, n⟩ : LargeEvenLabel)
        (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : X ⧸ Subgroup.center X ≃* R,
            (⟨.A, 1, 2 * n⟩ : LargeEvenLabel).tag = .A ∧ ggInducedAut θ δ ∈ I) := by
      refine largeEvenRawDatum_mono ?_ hraw
      rintro R _ I F ⟨hs, hna, θ, ⟨-, hI⟩, -⟩
      exact ⟨hs, hna, θ, rfl, hI⟩
    dsimp only [LargeEvenRawDatum] at h'
    obtain ⟨K, i1, i2, hK, hq⟩ := h'
    exact ⟨K, i1, i2, by rw [hK, ← pow_mul, mul_comm], hq⟩
  · by_cases hr3 : r = 3
    · subst hr3
      refine ggTorsionKnownOverTagsE67_typeTwA p X hX δ J
        ⟨hp, hp2, hδp, hδ1, hcomp, hXc, ⟨.twA, 3, n⟩,
          ⟨hn1, by norm_num, fun h => absurd h (by norm_num)⟩, ?_⟩ hJ
      have h' : LargeEvenRawDatum (⟨.twD, 3, n⟩ : LargeEvenLabel)
          (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
            ∃ θ : X ⧸ Subgroup.center X ≃* R,
              (⟨.twA, 3, n⟩ : LargeEvenLabel).tag = .twA ∧ ggInducedAut θ δ ∈ I) := by
        refine largeEvenRawDatum_mono ?_ hraw
        rintro R _ I F ⟨hs, hna, θ, ⟨-, hI⟩, -⟩
        exact ⟨hs, hna, θ, rfl, hI⟩
      exact h'
    · dsimp only [LargeEvenRawDatumLegacy] at hraw
      rw [if_neg hr2', if_neg hr3] at hraw
      obtain ⟨K, _, _, hK, b, c, hbc, hs, hna, θ, ⟨-, hI⟩, hM⟩ := hraw
      have hM' : CFSG.Open.StatedClassicalModel
          (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) .POmegaMinus r 2 n := by
        have h0 := hM
        dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h0
        rw [if_neg hr2', if_neg hr3, if_neg hr2', if_neg hr3, if_neg hr2'] at h0
        exact h0.statedClassicalModel_of_ne_zero (by omega)
      have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
      have hJ' := ggTorsion_isComponentOf_image θ hcomp
      obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
      obtain ⟨t', n', f', hL⟩ := ggTorsion_pomega_components (Or.inr rfl) hM'
        (e67bcd_center_eq_bot hs hna) hp hp2 hδp' hI hJ'
      exact ggTorsion_not_markingE67_of_classical
        (Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩) hJ

theorem ggTorsionKnownOverTagsE67_ambBCD :
    GGTorsionKnownOverTags GGTorsionAmbBCD
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  have h := ggTorsionKnownOverTags_or
    (ggTorsionKnownOverTags_or ggTorsionKnownOverTagsE67_typeBC ggTorsionKnownOverTagsE67_typeD)
    ggTorsionKnownOverTagsE67_typeTwD
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  refine h p X hX δ J ⟨hp, hp2, hδp, hδ1, hcomp, hXc, lab, hlab, ?_⟩ hJ
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hP, hI⟩
  refine ⟨hs, hna, θ, ?_, hI⟩
  unfold GGTorsionAmbBCD at hP
  tauto

end TorsionE67BCD

end CFSG.StandardType
