module

public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Basic
public import CFSG.LocalAnalysis.StandardType.GGTorsionNoPSL
import CFSG.LocalAnalysis.StandardType.GGTorsionPSUComp
public import CFSG.LocalAnalysis.StandardType.GGTorsionLinear
public import CFSG.LocalAnalysis.StandardType.GGTorsionTwA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionE67Linear

private theorem te67_center_eq_bot {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

private theorem te67_two_pow_ne_three {f : ℕ} (hf : 1 ≤ f) : 2 ^ f ≠ 3 := by
  intro h
  have hdvd : 2 ∣ 2 ^ f := pow_dvd_pow 2 hf
  rw [h] at hdvd
  norm_num at hdvd

private theorem te67_psl_model {J : Type} [Group J] {d : ℕ} {D : Type} [Field D] [Finite D]
    {f : ℕ} (hf : 1 ≤ f) (hd : 2 ≤ d) (hD : Nat.card D = 2 ^ f)
    (h22 : ¬ (d = 2 ∧ 2 ^ f = 2))
    (e : J ⧸ Subgroup.center J ≃*
      Matrix.SpecialLinearGroup (Fin d) D ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) :
    CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .PSL d 2 f := by
  refine ⟨⟨Nat.prime_two, hf, hd, ?_, ?_⟩, D, inferInstance, inferInstance, hD, ⟨?_⟩⟩
  · intro hc
    exact h22 (Prod.mk.inj hc)
  · intro hc
    exact te67_two_pow_ne_three hf (Prod.mk.inj hc).2
  · exact e.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d D)

theorem ggTorsion_not_markingE67_psl
    {J : Type} [Group J] {d : ℕ} (hd : 2 ≤ d) {D : Type} [Field D] [Finite D] [CharP D 2]
    (e : J ⧸ Subgroup.center J ≃*
      Matrix.SpecialLinearGroup (Fin d) D ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) :
    ¬ LargeEvenMarking J fun lab _ _ _ _ _ =>
      lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 := by
  intro hJ
  have hcard := ggTorsion_markingE67_card hJ
  haveI : Fintype D := Fintype.ofFinite D
  obtain ⟨k, -, hk⟩ := FiniteField.card D 2
  have hkpos : 0 < (k : ℕ) := k.pos
  have hf : 1 ≤ (k : ℕ) := by omega
  have hDf : Nat.card D = 2 ^ (k : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hk
  by_cases h22 : d = 2 ∧ 2 ^ (k : ℕ) = 2
  ·
    exfalso
    have hproj : Nat.card (J ⧸ Subgroup.center J) =
        Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL d D)) :=
      Nat.card_congr
        (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d D)).toEquiv
    have hsix : Nat.card (J ⧸ Subgroup.center J) = 6 := by
      rw [hproj, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := D) (n := d)
        (by omega)]
      rw [h22.1, hDf, h22.2]
      norm_num [Finset.Icc_self, Finset.prod_singleton]
    have hle := hcard.2
    rw [hsix] at hle
    norm_num at hle
  · exact ggTorsion_not_markingE67_of_classical
      (Or.inl ⟨.PSL, d, (k : ℕ), te67_psl_model hf hd hDf h22 e⟩) hJ

theorem ggTorsionKnownOverTagsE67_typeA :
    GGTorsionKnownOverTags (fun lab => lab.tag = .A)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .A := by
    obtain ⟨R, _, I, F, -, -, θ, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  obtain rfl : t = .A := htag
  obtain ⟨-, hr1, hr2⟩ := hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, _, _, hF, hs, hna, θ, -, hI⟩ := hraw
  have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
  have hJ' := ggTorsion_isComponentOf_image θ hcomp
  obtain ⟨d, D, _, _, hd, hD2, -, ⟨e₁⟩⟩ :=
    ggTorsion_psl_components (m := r) (n := n) hF (te67_center_eq_bot hs hna) hp hp2 hδp' hI hJ'
  obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  haveI := hD2
  exact ggTorsion_not_markingE67_psl hd (e₂.trans e₁) hJ

theorem ggTorsionKnownOverTagsE67_typeTwA :
    GGTorsionKnownOverTags (fun lab => lab.tag = .twA)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .twA := by
    obtain ⟨R, _, I, F, -, -, θ, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  obtain rfl : t = .twA := htag
  obtain ⟨hn, hr1, hr2⟩ := hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, _, _, hK, hs, hna, θ, -, hI⟩ := hraw
  have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
  have hJ' := ggTorsion_isComponentOf_image θ hcomp
  obtain ⟨t', n', f', hL⟩ := ggTorsion_psu_components hn hr1 hr2 hK hp hp2 hδp' hI hJ'
  obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  exact ggTorsion_not_markingE67_of_classical
    (Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩) hJ

theorem ggTorsionKnownOverTagsE67_ambA :
    GGTorsionKnownOverTags GGTorsionAmbA
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :=
  ggTorsionKnownOverTags_or ggTorsionKnownOverTagsE67_typeA ggTorsionKnownOverTagsE67_typeTwA

end TorsionE67Linear

end CFSG.StandardType
