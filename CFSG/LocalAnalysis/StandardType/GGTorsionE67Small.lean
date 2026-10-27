module

public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Basic
public import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4
public import CFSG.LocalAnalysis.StandardType.GGTorsionSmallOrd
import CFSG.LocalAnalysis.StandardType.GGTorsionE67ExcOrders
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionE67Small

private theorem es_not_three_dvd_ordSuzuki {n : ℕ} (hn : Odd n) :
    ¬ 3 ∣ CFSG.Open.ordSuzuki (2 ^ n) := by
  have hq : 2 ^ n % 3 = 2 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk]
    have h4 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul]
      ring
    rw [h2, Nat.mul_mod, h4]
  have hq2 : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hq2p1 : ((2 ^ n) ^ 2 + 1) % 3 = 2 := by
    rw [Nat.add_mod, hq2]
  intro h3
  unfold CFSG.Open.ordSuzuki at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have hz : 2 ^ n % 3 = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    · have hz : ((2 ^ n) ^ 2 + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
      omega
  · have hz : (2 ^ n - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    have hle := Nat.mod_le (2 ^ n) 3
    rw [hq] at hle
    have hge : 1 ≤ 2 ^ n := by omega
    have hpow : 2 ^ n = (2 ^ n - 1) + 1 := by omega
    have : 2 ^ n % 3 = 1 := by
      rw [hpow, Nat.add_mod, hz] <;> norm_num
    omega

private theorem es_ordTwistedF4_le_pow28 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTwistedF4 q ≤ q ^ 28 := by
  rw [CFSG.Open.ordTwistedF4]
  have h6 : q ^ 6 + 1 ≤ 2 * q ^ 6 := by
    have : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have h4 : q ^ 4 - 1 ≤ q ^ 4 := Nat.sub_le _ _
  have h3 : q ^ 3 + 1 ≤ 2 * q ^ 3 := by
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have h1 : q - 1 ≤ q := Nat.sub_le _ _
  calc q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
      ≤ q ^ 12 * (2 * q ^ 6) * q ^ 4 * (2 * q ^ 3) * q :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h6) h4) h3) h1
    _ = 4 * q ^ 26 := by ring
    _ ≤ q ^ 28 := by
      have hq2 : 4 ≤ q ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      calc 4 * q ^ 26 ≤ q ^ 2 * q ^ 26 := Nat.mul_le_mul_right _ hq2
        _ = q ^ 28 := by rw [← pow_add]

private theorem ggTorsion_markingE67_card_ge_twF4
    {J : Type} [Group J] {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (h : LargeEvenMarking J fun lab _ _ _ _ _ =>
      lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hdeg : markDeg lab = (2 * a + 1) * m)
    (hhas : GGHasLabel lab (J ⧸ Subgroup.center J)) :
    (2 ^ (2 * a + 1)) ^ 70 ≤ Nat.card (J ⧸ Subgroup.center J) := by
  obtain ⟨-, labJ, hlabJ, hrawJ⟩ := largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, _hs, _hna, θ, hP, hM⟩ := largeEvenRawDatum_exists hrawJ
  have hasJ : GGHasLabel labJ (J ⧸ Subgroup.center J) := by
    refine largeEvenRawDatum_mono ?_ hrawJ
    intro R' _ I' F' h'
    obtain ⟨-, -, θ', -⟩ := h'
    exact ⟨θ'⟩
  have hIso : GGLabelIso labJ lab :=
    ggLabelRigidInput_holds labJ lab (J ⧸ Subgroup.center J) hlabJ hlab hasJ hhas
  have hEq : labJ = lab := eq_of_ggLabelIso_of_excE67 hIso hP
  have hcard : Nat.card (J ⧸ Subgroup.center J) = Nat.card R := Nat.card_congr θ.toEquiv
  obtain ⟨t, l, k⟩ := labJ
  have hP' : t = .E6 ∨ t = .twE6 ∨ t = .E7 := by simpa only using hP
  have hdegJ : markDeg (⟨t, l, k⟩ : LargeEvenLabel) = (2 * a + 1) * m := by
    rw [← hEq] at hdeg
    exact hdeg
  have hmarkDeg : markDeg (⟨t, l, k⟩ : LargeEvenLabel) = k := by
    rcases hP' with rfl | rfl | rfl <;> rfl
  have hk : k = (2 * a + 1) * m := by
    rw [hmarkDeg] at hdegJ
    exact hdegJ
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    have h1 : 1 ≤ 2 * a + 1 := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) h1
  have hqQ : 2 ^ (2 * a + 1) ≤ 2 ^ k := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
  rcases hP' with rfl | rfl | rfl
  · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordE6 (2 ^ k) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rw [hcard, hR]
    calc (2 ^ (2 * a + 1)) ^ 70 ≤ (2 ^ k) ^ 70 := Nat.pow_le_pow_left hqQ 70
      _ ≤ CFSG.Open.ordE6 (2 ^ k) := ggE67_pow70_le_ordE6 (le_trans hq hqQ)
  · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordTwistedE6 (2 ^ k) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rw [hcard, hR]
    calc (2 ^ (2 * a + 1)) ^ 70 ≤ (2 ^ k) ^ 70 := Nat.pow_le_pow_left hqQ 70
      _ ≤ CFSG.Open.ordTwistedE6 (2 ^ k) := ggE67_pow70_le_ordTwistedE6 (le_trans hq hqQ)
  · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordE7 (2 ^ k) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rw [hcard, hR]
    calc (2 ^ (2 * a + 1)) ^ 70 ≤ (2 ^ k) ^ 70 := Nat.pow_le_pow_left hqQ 70
      _ ≤ CFSG.Open.ordE7 (2 ^ k) := ggE67_pow70_le_ordE7 (le_trans hq hqQ)

private theorem ggTorsionKnownOverTagsE67_smallOrd :
    GGTorsionKnownOverTags
      (fun lab => lab.tag = .twB2 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, ⟨hP, -⟩, hM⟩ :=
    largeEvenMarking_exists_markedModel hmark
  obtain ⟨h3J, hJge⟩ := ggTorsion_markingE67_card hJ
  obtain ⟨H, hHne, hJdvdH⟩ := ggTorsion_dvd_proper hX θ hδ1 hcomp.1
  haveI : Finite R := Finite.of_equiv (X ⧸ Subgroup.center X) θ.toEquiv
  have hHdvdR : Nat.card ↥H ∣ Nat.card R := Subgroup.card_subgroup_dvd_card H
  have hHleR : Nat.card ↥H ≤ Nat.card R :=
    Nat.card_le_card_of_injective H.subtype H.subtype_injective
  have hHneR : Nat.card ↥H ≠ Nat.card R := by
    intro heq
    exact hHne ((Subgroup.card_eq_iff_eq_top H).1 heq)
  have hHltR : Nat.card ↥H < Nat.card R := lt_of_le_of_ne hHleR hHneR
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hJleH : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥H :=
    Nat.le_of_dvd hHpos hJdvdH
  have hgeH : 2 ^ 70 ≤ Nat.card ↥H := hJge.trans hJleH
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hP hlab
  rcases hP with rfl | rfl | rfl | rfl
  ·
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hn : Odd n := by
      dsimp only [LargeEvenInLambda2] at hlab
      exact hlab.2.2.1
    have hR : Nat.card R = CFSG.Open.ordSuzuki (2 ^ n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
      rfl
    have h3R : 3 ∣ Nat.card R := dvd_trans h3J (dvd_trans hJdvdH hHdvdR)
    rw [hR] at h3R
    exact es_not_three_dvd_ordSuzuki hn h3R
  ·
    have hR : Nat.card R = 360 :=
      ggMarkedModel_card_b2der (lab := ⟨.B2der, l, n⟩) rfl hM
    have hlt : Nat.card ↥H < 2 ^ 70 := by
      calc Nat.card ↥H < Nat.card R := hHltR
        _ = 360 := hR
        _ < 2 ^ 70 := by norm_num
    exact absurd hgeH (not_le_of_gt hlt)
  ·
    have hR : Nat.card R = 6048 :=
      CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der (lab := ⟨.G2der, l, n⟩) rfl hM
    have hlt : Nat.card ↥H < 2 ^ 70 := by
      calc Nat.card ↥H < Nat.card R := hHltR
        _ = 6048 := hR
        _ < 2 ^ 70 := by norm_num
    exact absurd hgeH (not_le_of_gt hlt)
  ·
    have hR : Nat.card R = CFSG.Open.ordTits :=
      CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_twF4der
        (lab := ⟨.twF4der, l, n⟩) rfl hM
    have hlt : Nat.card ↥H < 2 ^ 70 := by
      calc Nat.card ↥H < Nat.card R := hHltR
        _ = CFSG.Open.ordTits := hR
        _ < 2 ^ 70 := by norm_num [CFSG.Open.ordTits]
    exact absurd hgeH (not_le_of_gt hlt)

private theorem ggTorsionKnownOverTagsE67_typeTwF4 :
    GGTorsionKnownOverTags (fun lab => lab.tag = .twF4)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
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
  have hge := ggTorsion_markingE67_card_ge_twF4 ha hm hJ hlab' hdeg hhasJ
  rw [hn2] at hge
  obtain ⟨H, hHne, hJdvdH⟩ := ggTorsion_dvd_proper hX θ hδ1 hcomp.1
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Finite.of_equiv (X ⧸ Subgroup.center X) θ.toEquiv
  have hHleR : Nat.card ↥H ≤ Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Nat.card_le_card_of_injective H.subtype H.subtype_injective
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hJleH : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥H :=
    Nat.le_of_dvd hHpos hJdvdH
  have hHleOrd : Nat.card ↥H ≤ CFSG.Open.ordTwistedF4 (2 ^ n) := by
    rw [← hR]
    exact hHleR
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : (2 ^ n) ^ 70 ≤ CFSG.Open.ordTwistedF4 (2 ^ n) :=
    le_trans hge (le_trans hJleH hHleOrd)
  have hle' : (2 ^ n) ^ 70 ≤ (2 ^ n) ^ 28 :=
    le_trans hle (es_ordTwistedF4_le_pow28 hq)
  have hlt : (2 ^ n) ^ 28 < (2 ^ n) ^ 70 :=
    Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by norm_num : 1 < 2)) (by norm_num)
  exact absurd hle' (not_le_of_gt hlt)

theorem ggTorsionKnownOverTagsE67_small :
    GGTorsionKnownOverTags GGTorsionAmbSmall
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  have hsmall := ggTorsionKnownOverTagsE67_smallOrd
  have htwf4 := ggTorsionKnownOverTagsE67_typeTwF4
  refine ggTorsionKnownOverTags_mono (ggTorsionKnownOverTags_or htwf4 hsmall) ?_
  intro lab h
  simp only [GGTorsionAmbSmall] at h
  tauto

end TorsionE67Small

end CFSG.StandardType
