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

section TorsionExcE8

private theorem txe_pow_pred_le_pow_sub_one {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    q ^ (k - 1) ≤ q ^ k - 1 := by
  have hXpos : 1 ≤ q ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hpow : q ^ k = q ^ (k - 1) * q := by
    conv_lhs => rw [← hk']
    rw [pow_succ]
  rw [hpow]
  have hmul : q ^ (k - 1) * 2 ≤ q ^ (k - 1) * q := Nat.mul_le_mul_left _ hq
  have h2 : q ^ (k - 1) * 2 = q ^ (k - 1) + q ^ (k - 1) := by ring
  have : q ^ (k - 1) + 1 ≤ q ^ (k - 1) * q := by
    calc q ^ (k - 1) + 1 ≤ q ^ (k - 1) + q ^ (k - 1) := Nat.add_le_add_left hXpos _
      _ = q ^ (k - 1) * 2 := h2.symm
      _ ≤ q ^ (k - 1) * q := hmul
  omega

private theorem txe_pow_add_one_le_pow_succ {q k : ℕ} (hq : 2 ≤ q) :
    q ^ k + 1 ≤ q ^ (k + 1) := by
  have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  have hmul : q ^ k * 2 ≤ q ^ k * q := Nat.mul_le_mul_left _ hq
  have h2 : q ^ k * 2 = q ^ k + q ^ k := by ring
  omega

private theorem txe_poly_le_pow9 {q : ℕ} (hq : 2 ≤ q) : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
  have h4 : q ^ 4 + 1 ≤ q ^ 8 := by
    have h2 : 2 ≤ q ^ 4 := by
      calc 2 ≤ 16 := by norm_num
        _ = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    calc q ^ 4 + 1 ≤ q ^ 4 + q ^ 4 := Nat.add_le_add_left (Nat.one_le_pow _ _ (by omega)) _
      _ = 2 * q ^ 4 := by ring
      _ ≤ q ^ 4 * q ^ 4 := Nat.mul_le_mul_right _ h2
      _ = q ^ 8 := by ring
  calc q ^ 8 + q ^ 4 + 1 = q ^ 8 + (q ^ 4 + 1) := by ring
    _ ≤ q ^ 8 + q ^ 8 := Nat.add_le_add_left h4 _
    _ = 2 * q ^ 8 := by ring
    _ ≤ q * q ^ 8 := Nat.mul_le_mul_right _ hq
    _ = q ^ 9 := by ring

private theorem txe_pow240_le_ordE8 {q : ℕ} (hq : 2 ≤ q) : q ^ 240 ≤ CFSG.Open.ordE8 q := by
  rw [CFSG.Open.ordE8]
  have h30 := txe_pow_pred_le_pow_sub_one (q := q) (k := 30) hq (by norm_num)
  have h24 := txe_pow_pred_le_pow_sub_one (q := q) (k := 24) hq (by norm_num)
  have h20 := txe_pow_pred_le_pow_sub_one (q := q) (k := 20) hq (by norm_num)
  have h18 := txe_pow_pred_le_pow_sub_one (q := q) (k := 18) hq (by norm_num)
  have h14 := txe_pow_pred_le_pow_sub_one (q := q) (k := 14) hq (by norm_num)
  have h12 := txe_pow_pred_le_pow_sub_one (q := q) (k := 12) hq (by norm_num)
  have h8 := txe_pow_pred_le_pow_sub_one (q := q) (k := 8) hq (by norm_num)
  have h2 := txe_pow_pred_le_pow_sub_one (q := q) (k := 2) hq (by norm_num)
  have hmain : q ^ 120 * q ^ 29 * q ^ 23 * q ^ 19 * q ^ 17 * q ^ 13 * q ^ 11 * q ^ 7 * q ^ 1 ≤
      q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
        (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) := by
    gcongr <;> (first | exact h30 | exact h24 | exact h20 | exact h18 | exact h14 | exact h12 | exact h8 | exact h2 | exact Nat.sub_le _ _)
  calc q ^ 240 = q ^ 120 * q ^ 29 * q ^ 23 * q ^ 19 * q ^ 17 * q ^ 13 * q ^ 11 * q ^ 7 * q ^ 1 := by
        ring
    _ ≤ _ := hmain

private theorem txe_ordE8_mono {q Q : ℕ} (h : q ≤ Q) : CFSG.Open.ordE8 q ≤ CFSG.Open.ordE8 Q := by
  rw [CFSG.Open.ordE8, CFSG.Open.ordE8]
  gcongr <;> exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h _) 1

private theorem txe_ordE6_le_pow78 {q : ℕ} : CFSG.Open.ordE6 q ≤ q ^ 78 := by
  rw [CFSG.Open.ordE6]
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
        (q ^ 2 - 1) / Nat.gcd 3 (q - 1)
      ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
          (q ^ 2 - 1) := Nat.div_le_self _ _
    _ ≤ q ^ 36 * q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 78 := by ring

private theorem txe_ordTwistedE6_le_pow80 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTwistedE6 q ≤ q ^ 80 := by
  rw [CFSG.Open.ordTwistedE6]
  have h9 := txe_pow_add_one_le_pow_succ (q := q) (k := 9) hq
  have h5 := txe_pow_add_one_le_pow_succ (q := q) (k := 5) hq
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1) / Nat.gcd 3 (q + 1)
      ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
          (q ^ 2 - 1) := Nat.div_le_self _ _
    _ ≤ q ^ 36 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 6 * q ^ 2 := by
        gcongr <;> (first | exact h9 | exact h5 | exact Nat.sub_le _ _)
    _ = q ^ 80 := by ring

private theorem txe_ordE7_le_pow133 {q : ℕ} : CFSG.Open.ordE7 q ≤ q ^ 133 := by
  rw [CFSG.Open.ordE7]
  calc q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) / Nat.gcd 2 (q - 1)
      ≤ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
          (q ^ 6 - 1) * (q ^ 2 - 1) := Nat.div_le_self _ _
    _ ≤ q ^ 63 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 133 := by ring

private theorem txe_ordF4_le_pow52 {q : ℕ} : CFSG.Open.ordF4 q ≤ q ^ 52 := by
  rw [CFSG.Open.ordF4]
  calc q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 24 * q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 52 := by ring

private theorem txe_ordTrialityD4_le_pow29 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTrialityD4 q ≤ q ^ 29 := by
  rw [CFSG.Open.ordTrialityD4]
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * q ^ 9 * q ^ 6 * q ^ 2 := by
        gcongr
        · exact txe_poly_le_pow9 hq
        · exact Nat.sub_le _ _
        · exact Nat.sub_le _ _
    _ = q ^ 29 := by ring

private theorem txe_ordG2_le_pow14 {q : ℕ} : CFSG.Open.ordG2 q ≤ q ^ 14 := by
  rw [CFSG.Open.ordG2]
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 14 := by ring

private theorem txe_ordE6_le_ordE8 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordE6 q ≤ CFSG.Open.ordE8 q :=
  le_trans (txe_ordE6_le_pow78)
    (le_trans (Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 78 ≤ 240))
      (txe_pow240_le_ordE8 hq))

private theorem txe_ordTwistedE6_le_ordE8 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTwistedE6 q ≤ CFSG.Open.ordE8 q :=
  le_trans (txe_ordTwistedE6_le_pow80 hq)
    (le_trans (Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 80 ≤ 240))
      (txe_pow240_le_ordE8 hq))

private theorem txe_ordE7_le_ordE8 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordE7 q ≤ CFSG.Open.ordE8 q :=
  le_trans (txe_ordE7_le_pow133)
    (le_trans (Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 133 ≤ 240))
      (txe_pow240_le_ordE8 hq))

private theorem txe_ordF4_le_ordE8 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordF4 q ≤ CFSG.Open.ordE8 q :=
  le_trans (txe_ordF4_le_pow52)
    (le_trans (Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 52 ≤ 240))
      (txe_pow240_le_ordE8 hq))

private theorem txe_ordTrialityD4_le_ordE8 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTrialityD4 q ≤ CFSG.Open.ordE8 q :=
  le_trans (txe_ordTrialityD4_le_pow29 hq)
    (le_trans (Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 29 ≤ 240))
      (txe_pow240_le_ordE8 hq))

private theorem txe_ordG2_le_ordE8 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordG2 q ≤ CFSG.Open.ordE8 q :=
  le_trans (txe_ordG2_le_pow14)
    (le_trans (Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 14 ≤ 240))
      (txe_pow240_le_ordE8 hq))

private theorem txe_markDeg_of_tag {lab : LargeEvenLabel} (h : lab.tag = .E8) :
    markDeg lab = lab.n := by
  obtain ⟨t, r, n⟩ := lab
  cases h
  rfl

private theorem txe_lieModel_of_exc {lab : LargeEvenLabel} {R : Type} [Group R]
    (ht : GGTorsionAmbExc lab) (hM : MarkedModel lab R) :
    CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
  obtain ⟨t, r, n⟩ := lab
  have ht' : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨ t = .twE6 ∨ t = .triD4 ∨ t = .G2 := ht
  rcases ht' with h | h | h | h | h | h | h <;> (cases h; exact hM)

private theorem txe_card_eq_evenLieOrder_of_exc
    {lab : LargeEvenLabel} {R : Type} [Group R]
    (ht : GGTorsionAmbExc lab) (hM : MarkedModel lab R) :
    Nat.card R = CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab)
      (markDeg lab) :=
  CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (txe_lieModel_of_exc ht hM)

private theorem txe_card_eq_ordE8_of_tag
    {lab : LargeEvenLabel} {R : Type} [Group R]
    (h : lab.tag = .E8) (hM : MarkedModel lab R) :
    Nat.card R = CFSG.Open.ordE8 (2 ^ lab.n) := by
  obtain ⟨t, r, n⟩ := lab
  cases h
  exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM

private theorem txe_evenLieOrder_exc_le_ordE8 {t : CFSG.Open.StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨ t = .twistedE6 ∨ t = .trialityD4 ∨ t = .G2)
    {n : ℕ} (hn : 1 ≤ n) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder t 0 n ≤ CFSG.Open.ordE8 (2 ^ n) := by
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact txe_ordE6_le_ordE8 hq
  · exact txe_ordE7_le_ordE8 hq
  · exact le_rfl
  · exact txe_ordF4_le_ordE8 hq
  · exact txe_ordTwistedE6_le_ordE8 hq
  · exact txe_ordTrialityD4_le_ordE8 hq
  · exact txe_ordG2_le_ordE8 hq

private theorem txe_evenLieOrder_exc_le {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : GGTorsionAmbExc lab) {nT : ℕ} (hle : lab.n ≤ nT) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab) (markDeg lab) ≤
      CFSG.Open.ordE8 (2 ^ nT) := by
  obtain ⟨t, r, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  have ht' : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨ t = .twE6 ∨ t = .triD4 ∨ t = .G2 := ht
  have hmono : CFSG.Open.ordE8 (2 ^ n) ≤ CFSG.Open.ordE8 (2 ^ nT) :=
    txe_ordE8_mono (Nat.pow_le_pow_right (by norm_num) hle)
  rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact le_trans (txe_evenLieOrder_exc_le_ordE8 (Or.inl rfl) hn) hmono
  · exact le_trans (txe_evenLieOrder_exc_le_ordE8 (Or.inr (Or.inl rfl)) hn) hmono
  · exact le_trans (txe_evenLieOrder_exc_le_ordE8 (Or.inr (Or.inr (Or.inl rfl))) hn) hmono
  · exact le_trans (txe_evenLieOrder_exc_le_ordE8 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hn) hmono
  · exact le_trans
      (txe_evenLieOrder_exc_le_ordE8 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hn) hmono
  · exact le_trans
      (txe_evenLieOrder_exc_le_ordE8 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hn)
      hmono
  · exact le_trans
      (txe_evenLieOrder_exc_le_ordE8 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hn)
      hmono

theorem ggTorsionKnownOver_excE8Sr
    : GGTorsionKnownOverTags GGTorsionAmbExc
      (fun lab => lab.tag = .E8 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  have hFD := ggTorsion_exc_fieldData (P := GGTorsionAmbExc) (fun _ h => h)
    ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩
  obtain ⟨labA, hlabA, RA, _hgrpA, _IA, _FA, θA, _hsA, _hnaA, ⟨hPA, hfdA⟩, hMA⟩ :=
    largeEvenMarking_exists_markedModel hFD
  obtain ⟨-, labT, hlabT, hrawT⟩ := largeEvenMarking_markedModel hJ
  have hasJ : GGHasLabel labT (J ⧸ Subgroup.center J) := by
    refine largeEvenRawDatum_mono ?_ hrawT
    intro R _ I F h
    obtain ⟨-, -, θ, -⟩ := h
    exact ⟨θ⟩
  obtain ⟨RT, _hgrpT, _IT, _FT, _hsT, _hnaT, θT, hPT, hMT⟩ := largeEvenRawDatum_exists hrawT
  unfold GGCompFieldDataQ GGCompFieldAt at hfdA
  rcases hfdA with ⟨m, hm, labF, hlabF, _hchar, hdeg, _h1F, h2F, h3F, hhasF, _RF, _hgrpF, hMF, _⟩ |
    ⟨_hnA2, hcardOr⟩
  ·
    have hIso : GGLabelIso labT labF :=
      ggLabelRigidInput_holds labT labF (J ⧸ Subgroup.center J) hlabT hlabF hasJ hhasF
    have hPT' : GGL45TorsionTag labT := by
      simp only [GGL45TorsionTag]
      tauto
    have hEq : labT = labF := eq_of_ggLabelIso_of_torsionTag hIso hPT'
    have htagT : labT.tag = .E8 := by
      rcases hPT with h | h | h
      · exact h
      · exact absurd (hEq ▸ h) h2F
      · exact absurd (hEq ▸ h) h3F
    have hTFtag : labF.tag = .E8 := hEq ▸ htagT
    have hmarkDegF : markDeg labF = labF.n := txe_markDeg_of_tag hTFtag
    have hpow : 2 ^ labF.n = 2 ^ (labA.n * m) := by
      rw [← hmarkDegF, hdeg, ← pow_mul]
    have hnm : labF.n = labA.n * m := Nat.pow_right_injective (by norm_num) hpow
    have hnAle : labA.n ≤ labT.n := by
      have hlabTn : labT.n = labF.n := by rw [hEq]
      rw [hlabTn, hnm]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hcardA : Nat.card RA =
        CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag labA) (markRank labA)
          (markDeg labA) :=
      txe_card_eq_evenLieOrder_of_exc hPA hMA
    have hcardT : Nat.card RT = CFSG.Open.ordE8 (2 ^ labT.n) :=
      txe_card_eq_ordE8_of_tag htagT hMT
    have hRTgeRA : Nat.card RA ≤ Nat.card RT := by
      rw [hcardA, hcardT]
      exact txe_evenLieOrder_exc_le hlabA hPA hnAle
    obtain ⟨H, hHne, hJdvdH⟩ := ggTorsion_dvd_proper hX θA hδ1 hcomp.1
    haveI : Finite RA := Finite.of_equiv (X ⧸ Subgroup.center X) θA.toEquiv
    have hHleR : Nat.card ↥H ≤ Nat.card RA :=
      Nat.card_le_card_of_injective H.subtype H.subtype_injective
    have hHneR : Nat.card ↥H ≠ Nat.card RA := by
      intro heq
      exact hHne ((Subgroup.card_eq_iff_eq_top H).1 heq)
    have hHpos : 0 < Nat.card ↥H := Nat.card_pos
    have hJleH : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥H :=
      Nat.le_of_dvd hHpos hJdvdH
    have hcardJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card RT :=
      Nat.card_congr θT.toEquiv
    have hRTleH : Nat.card RT ≤ Nat.card ↥H := by
      rw [← hcardJ]
      exact hJleH
    have hHltR : Nat.card ↥H < Nat.card RA := lt_of_le_of_ne hHleR hHneR
    exact (not_le.mpr (lt_of_le_of_lt hRTleH hHltR)) hRTgeRA
  ·
    have hJtors : LargeEvenMarking J fun lab _ _ _ _ _ => GGL45TorsionTag lab :=
      largeEvenMarking_mono (fun lab _ _ _ _ _ h => by simp only [GGL45TorsionTag]; tauto) hJ
    have hge : 17971200 ≤ Nat.card (↥J ⧸ Subgroup.center ↥J) := (ggTorsion_marking_card hJtors).1
    rcases hcardOr with h360 | h6048
    · rw [h360] at hge
      norm_num at hge
    · rw [h6048] at hge
      norm_num at hge

end TorsionExcE8

end CFSG.StandardType
