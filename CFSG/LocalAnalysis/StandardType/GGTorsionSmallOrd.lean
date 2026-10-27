module

public import CFSG.LocalAnalysis.StandardType.GGTorsionQuot
public import CFSG.LocalAnalysis.StandardType.GGTorsionOrders
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

section TorsionSmallOrd

private theorem ts_not_three_dvd_ordSuzuki {n : ℕ} (hn : Odd n) :
    ¬ 3 ∣ ordSuzuki (2 ^ n) := by
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
  unfold ordSuzuki at h3
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

theorem ggTorsionKnownOver_smallOrd :
    GGTorsionKnownOver fun lab =>
      lab.tag = .twB2 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, ⟨hP, -⟩, hM⟩ :=
    largeEvenMarking_exists_markedModel hmark
  obtain ⟨hJge, h3J⟩ := ggTorsion_marking_card hJ
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
  have hgeH : 17971200 ≤ Nat.card ↥H := hJge.trans hJleH
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hP hlab
  rcases hP with rfl | rfl | rfl | rfl
  ·
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hn : Odd n := by
      dsimp only [LargeEvenInLambda2] at hlab
      exact hlab.2.2.1
    have hR : Nat.card R = ordSuzuki (2 ^ n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
      rfl
    have h3R : 3 ∣ Nat.card R := dvd_trans h3J (dvd_trans hJdvdH hHdvdR)
    rw [hR] at h3R
    exact ts_not_three_dvd_ordSuzuki hn h3R
  ·
    have hR : Nat.card R = 360 :=
      ggMarkedModel_card_b2der (lab := ⟨.B2der, l, n⟩) rfl hM
    omega
  ·
    have hR : Nat.card R = 6048 :=
      CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der (lab := ⟨.G2der, l, n⟩) rfl hM
    omega
  ·
    have hR : Nat.card R = ordTits :=
      CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_twF4der
        (lab := ⟨.twF4der, l, n⟩) rfl hM
    have hord : ordTits = 17971200 := by norm_num [ordTits]
    omega

end TorsionSmallOrd

end CFSG.StandardType
