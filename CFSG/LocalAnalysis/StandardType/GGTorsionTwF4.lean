module

public import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4Comp
public import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4Card
public import CFSG.LocalAnalysis.StandardType.GGTorsionQuot
public import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
public import CFSG.LocalAnalysis.StandardType.GGTorsionSmallOrd
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionTwF4

theorem ggTorsionKnownOver_typeTwF4 :
    GGTorsionKnownOver fun lab => lab.tag = .twF4 := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hmark
  have htag : lab.tag = .twF4 := by
    obtain ⟨R, _, I, F, -, -, θ, ⟨hP, -⟩, -⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, l, n⟩ := lab
  obtain rfl : t = .twF4 := htag
  dsimp only [LargeEvenInLambda2] at hlab
  obtain ⟨-, -, ⟨c, hc⟩, hn⟩ := hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, _, _, hK, hs, hna, θ, ⟨-, hI⟩, hM⟩ := hraw
  have ha : 1 ≤ (n - 1) / 2 := by omega
  have hn2 : 2 * ((n - 1) / 2) + 1 = n := by omega
  dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
  have hR : Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) =
      CFSG.Open.ordTwistedF4 (2 ^ n) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
  have hδ1' : ggInducedAut θ δ ≠ 1 := fun h =>
    hδ1 (ggInducedAut_injective_of_perfect hX θ (h.trans (map_one _).symm))
  have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
  have hδinn := chevIDImage_subset_inn_twF4 ha K hK hI
  have hJ' := ggTorsion_isComponentOf_image θ hcomp
  obtain ⟨m, lab', hm, hlab', -, hdeg, hhas⟩ :=
    ggTorsion_twF4_compField ha K hK hp hp2 hδ1' hδp' hδinn hJ'
  obtain ⟨e⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  have hhasJ : GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) :=
    largeEvenRawDatum_mono (fun R' _ _ _ ⟨f⟩ => ⟨e.trans f⟩) hhas
  have hge := ggTorsion_marking_card_ge_twF4 ha hm hJ hlab' hdeg hhasJ
  rw [hn2] at hge
  obtain ⟨H, hHne, hJdvdH⟩ := ggTorsion_dvd_proper hX θ hδ1 hcomp.1
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Finite.of_equiv (X ⧸ Subgroup.center X) θ.toEquiv
  have hHleR : Nat.card ↥H ≤ Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Nat.card_le_card_of_injective H.subtype H.subtype_injective
  have hHneR : Nat.card ↥H ≠ Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) := by
    intro heq
    exact hHne ((Subgroup.card_eq_iff_eq_top H).1 heq)
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hJleH : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥H := Nat.le_of_dvd hHpos hJdvdH
  omega

theorem ggTorsionKnownOver_or {P Q : LargeEvenLabel → Prop} (hP : GGTorsionKnownOver P)
    (hQ : GGTorsionKnownOver Q) : GGTorsionKnownOver fun lab => P lab ∨ Q lab := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have key : ∀ P' : LargeEvenLabel → Prop, P' lab → GGTorsionDatum P' p δ J := by
    intro P' hP'
    refine ⟨hp, hp2, hδp, hδ1, hcomp, hXc, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, -, hI⟩
    exact ⟨hs, hna, θ, hP', hI⟩
  obtain ⟨R, _, I, F, -, -, θ, ⟨hPQ, -⟩⟩ := largeEvenRawDatum_exists hraw
  rcases hPQ with h | h
  · exact hP p X hX δ J (key _ h) hJ
  · exact hQ p X hX δ J (key _ h) hJ

theorem ggTorsionKnownOver_small :
    GGTorsionKnownOver GGTorsionAmbSmall := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have h := ggTorsionKnownOver_or ggTorsionKnownOver_smallOrd ggTorsionKnownOver_typeTwF4
  refine h p X hX δ J ⟨hp, hp2, hδp, hδ1, hcomp, hXc, lab, hlab, ?_⟩ hJ
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hP, hI⟩
  refine ⟨hs, hna, θ, ?_, hI⟩
  simp only [GGTorsionAmbSmall] at hP
  tauto

end TorsionTwF4

end CFSG.StandardType
