module

public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Basic
public import CFSG.LocalAnalysis.StandardType.GGTorsionE67ExcOrders
public import CFSG.LocalAnalysis.StandardType.GGTorsionExcE8
import CFSG.LocalAnalysis.StandardType.GGTorsionQuot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionE67Exc

private theorem txe67_markDeg_of_tag {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) : markDeg lab = lab.n := by
  obtain ⟨t, r, n⟩ := lab
  rcases h with h | h | h <;> (cases h; rfl)

private theorem txe67_markChar_of_exc {lab : LargeEvenLabel} (hexc : GGTorsionAmbExc lab) :
    markChar lab = 2 := by
  obtain ⟨t, r, n⟩ := lab
  rcases hexc with h | h | h | h | h | h | h <;> (cases h; rfl)

private theorem txe67_card_eq_evenLieOrder_of_exc
    {lab : LargeEvenLabel} {R : Type} [Group R]
    (hexc : GGTorsionAmbExc lab) (hM : MarkedModel lab R) :
    Nat.card R = CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab)
      (markDeg lab) := by
  have hch : markChar lab = 2 := txe67_markChar_of_exc hexc
  exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (by rw [← hch]; exact hM)

private theorem txe67_pow70_le_card_of_tag
    {lab : LargeEvenLabel} {R : Type} [Group R]
    (hn : 1 ≤ lab.n) (hexc : GGTorsionAmbExc lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) (hM : MarkedModel lab R) :
    (2 ^ lab.n) ^ 70 ≤ Nat.card R := by
  have hq : 2 ≤ 2 ^ lab.n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  rw [txe67_card_eq_evenLieOrder_of_exc hexc hM]
  obtain ⟨t, r, n⟩ := lab
  rcases htag with h | h | h
  · cases h
    show (2 ^ n) ^ 70 ≤ CFSG.Open.ordE6 (2 ^ n)
    exact ggE67_pow70_le_ordE6 hq
  · cases h
    show (2 ^ n) ^ 70 ≤ CFSG.Open.ordTwistedE6 (2 ^ n)
    exact ggE67_pow70_le_ordTwistedE6 hq
  · cases h
    show (2 ^ n) ^ 70 ≤ CFSG.Open.ordE7 (2 ^ n)
    exact ggE67_pow70_le_ordE7 hq

private theorem txe67_card_le_pow52
    {lab : LargeEvenLabel} {R : Type} [Group R]
    (hn : 1 ≤ lab.n) (hexc : GGTorsionAmbExc lab)
    (hP : lab.tag = .F4 ∨ lab.tag = .triD4 ∨ lab.tag = .G2) (hM : MarkedModel lab R) :
    Nat.card R ≤ (2 ^ lab.n) ^ 52 := by
  have hq : 2 ≤ 2 ^ lab.n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  rw [txe67_card_eq_evenLieOrder_of_exc hexc hM]
  obtain ⟨t, r, n⟩ := lab
  rcases hP with h | h | h
  · cases h
    show CFSG.Open.ordF4 (2 ^ n) ≤ (2 ^ n) ^ 52
    exact ggE67_ordF4_le_pow52
  · cases h
    show CFSG.Open.ordTrialityD4 (2 ^ n) ≤ (2 ^ n) ^ 52
    exact le_trans (ggE67_ordTrialityD4_le_ordF4 hq) ggE67_ordF4_le_pow52
  · cases h
    show CFSG.Open.ordG2 (2 ^ n) ≤ (2 ^ n) ^ 52
    exact le_trans (ggE67_ordG2_le_ordF4 hq) ggE67_ordF4_le_pow52

theorem ggTorsionKnownOverTagsE67_exc
    : GGTorsionKnownOverTags
      (fun lab => lab.tag = .F4 ∨ lab.tag = .triD4 ∨ lab.tag = .G2)
      (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  have hFD := ggTorsion_exc_fieldData
    (P := fun lab => lab.tag = .F4 ∨ lab.tag = .triD4 ∨ lab.tag = .G2)
    (fun lab h => by rcases h with h | h | h <;> simp [GGTorsionAmbExc, h])
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
  rcases hfdA with ⟨m, hm, labF, hlabF, _hchar, hdeg, _h1F, h2F, h3F, hhasF, _RF, _hgrpF, _hMF, _⟩ |
    ⟨_hnA2, hcardOr⟩
  · have hexcA : GGTorsionAmbExc labA := by
      rcases hPA with h | h | h <;> simp [GGTorsionAmbExc, h]
    have hexcT : GGTorsionAmbExc labT := by
      rcases hPT with h | h | h <;> simp [GGTorsionAmbExc, h]
    have hIso : GGLabelIso labT labF :=
      ggLabelRigidInput_holds labT labF (J ⧸ Subgroup.center J) hlabT hlabF hasJ hhasF
    have hEq : labT = labF := eq_of_ggLabelIso_of_excE67 hIso hPT
    have hTFtag : labF.tag = .E6 ∨ labF.tag = .twE6 ∨ labF.tag = .E7 := hEq ▸ hPT
    have hmarkDegF : markDeg labF = labF.n := txe67_markDeg_of_tag hTFtag
    have hpow : 2 ^ labF.n = 2 ^ (labA.n * m) := by
      rw [← hmarkDegF, hdeg, ← pow_mul]
    have hnm : labF.n = labA.n * m := Nat.pow_right_injective (by norm_num) hpow
    have hlabTn : labT.n = labA.n * m := by rw [hEq, hnm]
    have hRTpow : (2 ^ labT.n) ^ 70 ≤ Nat.card RT :=
      txe67_pow70_le_card_of_tag hlabT.1 hexcT hPT hMT
    have hRAlt : Nat.card RA < Nat.card RT := by
      have hleA : Nat.card RA ≤ (2 ^ labA.n) ^ 52 :=
        txe67_card_le_pow52 hlabA.1 hexcA hPA hMA
      have hq1 : 1 < 2 ^ labA.n := by
        calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ labA.n := Nat.pow_le_pow_right (by norm_num) hlabA.1
      have hlt : (2 ^ labA.n) ^ 52 < (2 ^ labA.n) ^ 70 :=
        Nat.pow_lt_pow_right hq1 (by norm_num)
      have hqle : (2 ^ labA.n) ^ 70 ≤ (2 ^ labT.n) ^ 70 := by
        rw [hlabTn]
        exact Nat.pow_le_pow_left
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))) 70
      exact lt_of_le_of_lt hleA (lt_of_lt_of_le hlt (le_trans hqle hRTpow))
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
    exact absurd (lt_of_le_of_lt hRTleH hHltR) (not_lt_of_ge (le_of_lt hRAlt))
  · have hge : 2 ^ 70 ≤ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
      (ggTorsion_markingE67_card hJ).2
    rcases hcardOr with h360 | h6048
    · rw [h360] at hge
      norm_num at hge
    · rw [h6048] at hge
      norm_num at hge

end TorsionE67Exc

end CFSG.StandardType
