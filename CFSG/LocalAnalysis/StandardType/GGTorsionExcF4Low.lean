module

public import CFSG.LocalAnalysis.StandardType.GGTorsionExcDefs
public import CFSG.LocalAnalysis.StandardType.GGTorsionExcField
import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4Card
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.GGTorsionQuot
import CFSG.LocalAnalysis.StandardType.GGTorsionOrders
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionExcF4Low

private theorem txg_pow_sub_one_pos {Q k : ℕ} (hQ : 2 ≤ Q) (hk : k ≠ 0) : 0 < Q ^ k - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hk (by omega))

private theorem txg_pow28_le_ordF4 {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 28 ≤ CFSG.Open.ordF4 Q := by
  rw [CFSG.Open.ordF4]
  have h12 : Q ^ 4 ≤ Q ^ 12 - 1 := by
    have h2 : Q ^ 12 = Q ^ 4 * Q ^ 8 := by rw [show 12 = 4 + 8 by norm_num, pow_add]
    have hlt8 : 1 < Q ^ 8 := Nat.one_lt_pow (by norm_num) (by omega)
    have hpos : 0 < Q ^ 4 := Nat.pow_pos (by omega)
    have hlt : Q ^ 4 < Q ^ 12 := by
      calc Q ^ 4 = Q ^ 4 * 1 := by ring
        _ < Q ^ 4 * Q ^ 8 := Nat.mul_lt_mul_of_pos_left hlt8 hpos
        _ = Q ^ 12 := h2.symm
    omega
  have h8 : 0 < Q ^ 8 - 1 := txg_pow_sub_one_pos hQ (by norm_num)
  have h6 : 0 < Q ^ 6 - 1 := txg_pow_sub_one_pos hQ (by norm_num)
  have h2 : 0 < Q ^ 2 - 1 := txg_pow_sub_one_pos hQ (by norm_num)
  calc Q ^ 28
      ≤ Q ^ 24 * Q ^ 4 := by rw [show 28 = 24 + 4 by norm_num, pow_add]
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) := Nat.mul_le_mul_left _ h12
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) := Nat.le_mul_of_pos_right _ h8
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) := Nat.le_mul_of_pos_right _ h6
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
          Nat.le_mul_of_pos_right _ h2

private theorem txg_ordF4_mono {q Q : ℕ} (h : q ≤ Q) :
    CFSG.Open.ordF4 q ≤ CFSG.Open.ordF4 Q := by
  rw [CFSG.Open.ordF4, CFSG.Open.ordF4]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left h 24)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 12) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 8) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 6) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

private theorem txg_ordG2_le_ordF4 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordG2 q ≤ CFSG.Open.ordF4 q := by
  have h14 : CFSG.Open.ordG2 q ≤ q ^ 14 := by
    rw [CFSG.Open.ordG2]
    calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
        ≤ q ^ 6 * q ^ 6 * q ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left (q ^ 6) (Nat.sub_le (q ^ 6) 1))
            (Nat.sub_le (q ^ 2) 1)
      _ = q ^ 14 := by ring
  have h1428 : q ^ 14 ≤ q ^ 28 := Nat.pow_le_pow_right (by omega) (by norm_num)
  exact le_trans h14 (le_trans h1428 (txg_pow28_le_ordF4 hq))

private theorem txg_ordTrialityD4_le_ordF4 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTrialityD4 q ≤ CFSG.Open.ordF4 q := by
  rw [CFSG.Open.ordTrialityD4, CFSG.Open.ordF4]
  have hA : q ^ 8 + q ^ 4 + 1 ≤ q ^ 12 := by
    have h1 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : 1 ≤ q ^ 8 := Nat.one_le_pow 8 q (by omega)
    have h3 : 3 ≤ q ^ 4 := by
      calc 3 ≤ 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have hsum : q ^ 8 + q ^ 4 + 1 ≤ 3 * q ^ 8 := by omega
    calc q ^ 8 + q ^ 4 + 1 ≤ 3 * q ^ 8 := hsum
      _ ≤ q ^ 4 * q ^ 8 := Nat.mul_le_mul_right _ h3
      _ = q ^ 12 := by ring
  have hstep1 : q ^ 12 * (q ^ 8 + q ^ 4 + 1) ≤ q ^ 24 := by
    calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) ≤ q ^ 12 * q ^ 12 := Nat.mul_le_mul_left _ hA
      _ = q ^ 24 := by ring
  have hD : 0 < q ^ 12 - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have hE : 0 < q ^ 8 - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have hstep2 : q ^ 24 ≤ q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) := by
    calc q ^ 24 ≤ q ^ 24 * (q ^ 12 - 1) := Nat.le_mul_of_pos_right _ hD
      _ ≤ q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) := Nat.le_mul_of_pos_right _ hE
  have hstep : q ^ 12 * (q ^ 8 + q ^ 4 + 1) ≤ q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) :=
    le_trans hstep1 hstep2
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ (q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1)) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
        Nat.mul_le_mul_right (q ^ 2 - 1) (Nat.mul_le_mul_right (q ^ 6 - 1) hstep)

theorem ggTorsionKnownOver_excLowF4
    : GGTorsionKnownOverTags (fun lab => lab.tag = .F4 ∨ lab.tag = .G2 ∨ lab.tag = .triD4)
      (fun lab => lab.tag = .F4) := by
  intro p X _ _ hX δ J hdat hJ
  have hFD := ggTorsion_exc_fieldData
    (P := fun lab => lab.tag = .F4 ∨ lab.tag = .G2 ∨ lab.tag = .triD4)
    (fun lab h => by simp only [GGTorsionAmbExc]; tauto) hdat
  obtain ⟨-, -, -, hδ1, hcomp, -⟩ := hdat
  obtain ⟨labA, hlabA, RA, _hRAgrp, IA, FA, θA, _hsimpleA, _hnaA, hPA, hMA⟩ :=
    largeEvenMarking_exists_markedModel hFD
  obtain ⟨hPA_tag, hField⟩ := hPA
  have hnA : 1 ≤ labA.n := hlabA.1
  have hqA : 2 ≤ 2 ^ labA.n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ labA.n := Nat.pow_le_pow_right (by norm_num) hnA
  have hcardRA : Nat.card RA ≤ CFSG.Open.ordF4 (2 ^ labA.n) := by
    rcases hPA_tag with hA | hA | hA
    · have h' := hMA
      dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h'
      rw [hA] at h'
      have hR : Nat.card RA = CFSG.Open.ordF4 (2 ^ labA.n) :=
        CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder h'
      exact le_of_eq hR
    · have h' := hMA
      dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h'
      rw [hA] at h'
      have hR : Nat.card RA = CFSG.Open.ordG2 (2 ^ labA.n) :=
        CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder h'
      rw [hR]
      exact txg_ordG2_le_ordF4 hqA
    · have h' := hMA
      dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h'
      rw [hA] at h'
      have hR : Nat.card RA = CFSG.Open.ordTrialityD4 (2 ^ labA.n) :=
        CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder h'
      rw [hR]
      exact txg_ordTrialityD4_le_ordF4 hqA
  have hJtors : LargeEvenMarking J fun lab _ _ _ _ _ => GGL45TorsionTag lab :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => by simp only [GGL45TorsionTag]; tauto) hJ
  have hcard_mark : 17971200 ≤ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    (ggTorsion_marking_card hJtors).1
  obtain ⟨-, labT, hlabT, hrawT⟩ := largeEvenMarking_markedModel hJ
  obtain ⟨RT, _hRTgrp, IT, FT, _hsimpleT, _hnaT, θT, htagT, hMT⟩ :=
    largeEvenRawDatum_exists hrawT
  have hasJT : GGHasLabel labT (↥J ⧸ Subgroup.center ↥J) := by
    refine largeEvenRawDatum_mono ?_ hrawT
    intro R _ I F h
    obtain ⟨-, -, θ, -⟩ := h
    exact ⟨θ⟩
  have htagTorsion : GGL45TorsionTag labT := by
    simp only [GGL45TorsionTag]
    exact Or.inr (Or.inl htagT)
  have hcardT : Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card RT := Nat.card_congr θT.toEquiv
  have hcardRT : Nat.card RT = CFSG.Open.ordF4 (2 ^ labT.n) := by
    have h' := hMT
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h'
    rw [htagT] at h'
    exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder h'
  rcases hField with ⟨m, hm, hAt⟩ | ⟨-, hsmall⟩
  · obtain ⟨labF, hlabF, -, hdegF, -, -, -, hhasF, -, -, -, -⟩ := hAt
    have hIso : GGLabelIso labT labF :=
      ggLabelRigidInput_holds labT labF (↥J ⧸ Subgroup.center ↥J) hlabT hlabF hasJT hhasF
    have hEq : labT = labF := eq_of_ggLabelIso_of_torsionTag hIso htagTorsion
    have hdegT : markDeg labT = labT.n := by
      simp only [markDeg, htagT]
    have hpowT : 2 ^ labT.n = (2 ^ labA.n) ^ m := by
      calc 2 ^ labT.n = 2 ^ markDeg labT := by rw [hdegT]
        _ = 2 ^ markDeg labF := by rw [← hEq]
        _ = (2 ^ labA.n) ^ m := hdegF
    have hmono : CFSG.Open.ordF4 (2 ^ labA.n) ≤ CFSG.Open.ordF4 (2 ^ labT.n) := by
      rw [hpowT]
      exact txg_ordF4_mono (by
        calc 2 ^ labA.n = (2 ^ labA.n) ^ 1 := (pow_one _).symm
          _ ≤ (2 ^ labA.n) ^ m :=
              Nat.pow_le_pow_right (Nat.one_le_pow labA.n 2 (by norm_num)) hm)
    have hcardRleJ : Nat.card RA ≤ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
      calc Nat.card RA ≤ CFSG.Open.ordF4 (2 ^ labA.n) := hcardRA
        _ ≤ CFSG.Open.ordF4 (2 ^ labT.n) := hmono
        _ = Nat.card RT := hcardRT.symm
        _ = Nat.card (↥J ⧸ Subgroup.center ↥J) := hcardT.symm
    obtain ⟨H, hHne, hJdvdH⟩ := ggTorsion_dvd_proper hX θA hδ1 hcomp.1
    haveI : Finite RA := Finite.of_equiv (X ⧸ Subgroup.center X) θA.toEquiv
    have hHleR : Nat.card ↥H ≤ Nat.card RA :=
      Nat.card_le_card_of_injective H.subtype H.subtype_injective
    have hHneR : Nat.card ↥H ≠ Nat.card RA := by
      intro heq
      exact hHne ((Subgroup.card_eq_iff_eq_top H).1 heq)
    have hHltR : Nat.card ↥H < Nat.card RA := lt_of_le_of_ne hHleR hHneR
    have hJleH : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥H :=
      Nat.le_of_dvd Nat.card_pos hJdvdH
    omega
  · rcases hsmall with h360 | h6048
    · rw [h360] at hcard_mark
      norm_num at hcard_mark
    · rw [h6048] at hcard_mark
      norm_num at hcard_mark

end TorsionExcF4Low

end CFSG.StandardType
