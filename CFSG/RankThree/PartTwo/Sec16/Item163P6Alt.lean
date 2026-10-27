module

public import CFSG.RankThree.PartTwo.Sec16.Item163P6Conf
public import CFSG.RankThree.PartTwo.Sec16.Item163P6Act
public import CFSG.RankThree.PartTwo.KFacts.KS163P6
import CFSG.RankThree.PartTwo.Sec16.Item163P6Shape
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem center_quot_eq_bot_of_alternating {Y : Subgroup G}
    (hK : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) :
    Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
  obtain ⟨e⟩ := hK
  rw [← Subgroup.map_center_eq e.symm, alternatingGroup.center_eq_bot (by simp),
    Subgroup.map_bot]

namespace Conf685

variable {A : Subgroup G} {c : G} {L Y S : Subgroup G}

private theorem map_actQ_le_normalizer {Y M A : Subgroup G}
    (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hMN : M ≤ Subgroup.normalizer (Y : Set G)) :
    (A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y) ≤
      Subgroup.normalizer (((M.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)) :
        Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y))) := by
  calc (A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)
      ≤ ((Subgroup.normalizer M).subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y) :=
        Subgroup.map_mono
          (Subgroup.subgroupOf_mono (Subgroup.normalizer (Y : Set G)) hAM)
    _ = (Subgroup.normalizer (M.subgroupOf (Subgroup.normalizer (Y : Set G)))).map (actQ Y) := by
        rw [Subgroup.subgroupOf_normalizer_eq hMN]
    _ ≤ Subgroup.normalizer (((M.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)) :
          Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y))) :=
        Subgroup.le_normalizer_map (actQ Y)

private theorem card_map_actQ_image_eq_one_or_four {Y M A : Subgroup G}
    (hA10 : KFacts.KS163P6A10)
    (hK : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)))
    (hAe : CFSG.Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hAY : A ≤ Y) (hAQ : A ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)
    (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hMN : M ≤ Subgroup.normalizer (Y : Set G))
    (hM2 : IsPGroup 2 (M.subgroupOf (Subgroup.normalizer (Y : Set G)))) :
    Nat.card ((M.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)) = 1 ∨
      Nat.card ((M.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)) = 4 := by
  have hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
    center_quot_eq_bot_of_alternating hK
  have hBelem : CFSG.Open.IsElemAbelian 3
      ((A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)) :=
    CFSG.Open.IsElemAbelian.map
      (CFSG.Open.IsElemAbelian.subgroupOf hAe (Subgroup.normalizer (Y : Set G))) (actQ Y)
  have hBcard : Nat.card
      ((A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)) = 27 := by
    rw [card_map_actQ_eq hZ hAY hAQ, hAcard]
  exact hA10 (↥Y ⧸ CFSG.pCore 2 ↥Y) hK
    ((A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y)) hBelem hBcard
    ((M.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actQ Y))
    (hM2.map (actQ Y)) (map_actQ_le_normalizer hAM hMN)

private theorem card_inf_eq_four (h : Conf685 A c L Y S) (hA10 : KFacts.KS163P6A10)
    {Y' : Subgroup G} (hY' : Y' ∈ scriptY0Star A (lB A))
    (hK : Nonempty (↥Y' ⧸ CFSG.pCore 2 ↥Y' ≃* alternatingGroup (Fin 10))) (hAY : A ≤ Y') :
    Nat.card (S ⊓ L : Subgroup G) = 4 ∧
      Nat.card (((S ⊓ L).subgroupOf (Subgroup.normalizer (Y' : Set G))).map
        (actQ Y')) = 4 := by
  have hAe : CFSG.Open.IsElemAbelian 3 A := h.sec15R.toSec13Data.isElemAbelian
  have hAcard : Nat.card A = 27 := h.sec15R.toSec13Data.card_eq
  have hAQ : A ⊓ CFSG.Open.pCoreOf 2 Y' = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) A
      (CFSG.Open.pCoreOf 2 Y') (CFSG.Open.IsElemAbelian.isPGroup hAe)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y'))
  have hDY : S ⊓ L ≤ Y' := inf_le_right.trans (h.le_y Y' hY')
  have hDQ : (S ⊓ L) ⊓ CFSG.Open.pCoreOf 2 Y' = ⊥ := by
    refine le_bot_iff.mp ?_
    calc (S ⊓ L) ⊓ CFSG.Open.pCoreOf 2 Y' ≤ L ⊓ CFSG.Open.pCoreOf 2 Y' :=
          inf_le_inf_right _ inf_le_right
      _ = ⊥ := inf_pCoreOf_eq_bot h hY'
  have hAD : A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (mem_scriptQ_iff.mp h.mem_d.prop.1.1).2.1
  have hD2 : IsPGroup 2 (S ⊓ L : Subgroup G) :=
    (isPiSubgroup_piOf_iff Nat.prime_two (S ⊓ L)).mp h.mem_d.prop.2
  have hD2' : IsPGroup 2 ((S ⊓ L).subgroupOf (Subgroup.normalizer (Y' : Set G))) :=
    hD2.comap_subtype (K := Subgroup.normalizer (Y' : Set G))
  have hTcard : Nat.card
      (((S ⊓ L).subgroupOf (Subgroup.normalizer (Y' : Set G))).map (actQ Y')) =
        Nat.card (S ⊓ L : Subgroup G) :=
    card_map_actQ_eq (center_quot_eq_bot_of_alternating hK) hDY hDQ
  have hfour := card_map_actQ_image_eq_one_or_four hA10 hK hAe hAcard hAY hAQ hAD
    (hDY.trans Subgroup.le_normalizer) hD2'
  rcases hfour with h1 | h4
  · have hcard1 : Nat.card (S ⊓ L : Subgroup G) = 1 := hTcard.symm.trans h1
    exact absurd hcard1 fun hc =>
      h.d_ne_bot ((Subgroup.eq_bot_iff_card (H := (S ⊓ L : Subgroup G))).mpr hc)
  · exact ⟨hTcard.symm.trans h4, h4⟩

theorem exists_actQ_eq_one_of_alternating {A : Subgroup G} {c : G} {L Y S : Subgroup G}
    (h : Conf685 A c L Y S) (hA10 : KFacts.KS163P6A10) {Y' R : Subgroup G}
    (hY' : Y' ∈ scriptY0Star A (lB A)) (hR : R ∈ scriptQPi A (lB A) ⊤ (piOf 2))
    (hRY : R ≤ Subgroup.normalizer (Y' : Set G)) (hDR : S ⊓ L < R)
    (hK : Nonempty (↥Y' ⧸ CFSG.pCore 2 ↥Y' ≃* alternatingGroup (Fin 10))) (hAY : A ≤ Y') :
    ∃ r ∈ R, r ≠ 1 ∧ ∃ hr : r ∈ Subgroup.normalizer (Y' : Set G),
      actQ Y' ⟨r, hr⟩ = 1 := by
  obtain ⟨hD4, hT4⟩ := card_inf_eq_four h hA10 hY' hK hAY
  have hAe : CFSG.Open.IsElemAbelian 3 A := h.sec15R.toSec13Data.isElemAbelian
  have hAcard : Nat.card A = 27 := h.sec15R.toSec13Data.card_eq
  have hAQ : A ⊓ CFSG.Open.pCoreOf 2 Y' = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) A
      (CFSG.Open.pCoreOf 2 Y') (CFSG.Open.IsElemAbelian.isPGroup hAe)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y'))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    (mem_scriptQ_iff.mp hR.1.1).2.1
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hR.2
  have hU2 : IsPGroup 2 (R.subgroupOf (Subgroup.normalizer (Y' : Set G))) :=
    hR2.comap_subtype (K := Subgroup.normalizer (Y' : Set G))
  have hDU : ((S ⊓ L).subgroupOf (Subgroup.normalizer (Y' : Set G))).map (actQ Y') ≤
      (R.subgroupOf (Subgroup.normalizer (Y' : Set G))).map (actQ Y') :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono (Subgroup.normalizer (Y' : Set G)) hDR.le)
  have hdvd : Nat.card
      (((S ⊓ L).subgroupOf (Subgroup.normalizer (Y' : Set G))).map (actQ Y')) ∣
        Nat.card ((R.subgroupOf (Subgroup.normalizer (Y' : Set G))).map (actQ Y')) :=
    Subgroup.card_dvd_of_le hDU
  rw [hT4] at hdvd
  have hU4 : Nat.card
      ((R.subgroupOf (Subgroup.normalizer (Y' : Set G))).map (actQ Y')) = 4 := by
    rcases card_map_actQ_image_eq_one_or_four hA10 hK hAe hAcard hAY hAQ hAR hRY hU2 with
      h1 | h4
    · rw [h1] at hdvd
      exact absurd (Nat.dvd_one.mp hdvd) (by norm_num)
    · exact h4
  have hlt : Nat.card
      ((R.subgroupOf (Subgroup.normalizer (Y' : Set G))).map (actQ Y')) < Nat.card R := by
    rw [hU4, ← hD4]
    exact Subgroup.card_lt_of_lt hDR
  exact exists_actQ_eq_one_of_card_lt hRY hlt

end Conf685

end CFSG.RankThree.PartTwo.Sec16.Proof163P6

end
