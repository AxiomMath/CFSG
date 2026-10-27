module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.LocalAnalysis.StandardType.GGTorsionPOmegaComp
import CFSG.LocalAnalysis.StandardType.GGTorsionClassical
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.GGTorsionLinear
import CFSG.LocalAnalysis.StandardType.GGTorsionTwA
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionOrth

private theorem tor_center_eq_bot {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem ggTorsionKnownOver_typeD :
    GGTorsionKnownOver fun lab => lab.tag = .D := by
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
    refine ggTorsionKnownOver_typeA p X hX δ J
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
      (tor_center_eq_bot hs hna) hp hp2 hδp' hI hJ'
    exact ggTorsion_not_marking_of_classical
      (Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩) hJ

theorem ggTorsionKnownOver_typeTwD :
    GGTorsionKnownOver fun lab => lab.tag = .twD := by
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
    refine ggTorsionKnownOver_typeA p X hX δ J
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
      refine ggTorsionKnownOver_typeTwA p X hX δ J
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
        (tor_center_eq_bot hs hna) hp hp2 hδp' hI hJ'
      exact ggTorsion_not_marking_of_classical
        (Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩) hJ

end TorsionOrth

end CFSG.StandardType
