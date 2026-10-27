module

public import CFSG.Timmesfeld.Transvection.ResidueBender
public import CFSG.Timmesfeld.Transvection.ResidueQuadrangle
import CFSG.Timmesfeld.Transvection.Small
import CFSG.Timmesfeld.Transvection.LineConjugates
import CFSG.Timmesfeld.Transvection.FrameLineCard
import CFSG.Combinatorics.QuadrangleGraphOrder
import CFSG.Combinatorics.QuadrangleGraphThas

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Combinatorics.QuadrangleGraph

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}

section

theorem IsMaxFrame.ncard_frameResidue_eq_of_ne [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hthick : ThickLines Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k) :
    (frameResidue Δ P Q j).ncard = (frameResidue Δ P Q k).ncard := by
  classical
  letI : Fintype ↥(rankTwoResidue Δ P Q j k) := Fintype.ofFinite _
  have hT := hF.isThickQuadrangle_residueAdj hΔ hpts hML hthick hjk
  have hPQk : ¬ residueAdj Δ P Q j k
      ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩
      ⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_right j k⟩ :=
    ModelRank.not_commuting_of_opposite (hF.opposite k)
  have hPQj : ¬ residueAdj Δ P Q j k
      ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩ :=
    ModelRank.not_commuting_of_opposite (hF.opposite j)
  calc (frameResidue Δ P Q j).ncard
      = (perp2 (residueAdj Δ P Q j k) ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩
          ⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_right j k⟩).card :=
        (hF.toIsFrame.card_perp2_residueAdj_PQ hjk).symm
    _ = (perp2 (residueAdj Δ P Q j k) ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
          ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card :=
        hT.card_perp2_eq hPQk hPQj
    _ = (frameResidue Δ P Q k).ncard :=
        hF.toIsFrame.card_perp2_residueAdj_PQ_left hjk

private theorem exists_span_data [Finite H] (hΔ : IsTransvectionClass Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} [Fintype ↥(rankTwoResidue Δ P Q j k)] {s t : ℕ}
    (hO : IsQuadrangleOfOrder (residueAdj Δ P Q j k) s t) (hs2 : 2 ≤ s) (ht1 : 1 ≤ t) :
    ∃ p, Nat.card (P k) ≤ p ∧
      (span2 (residueAdj Δ P Q j k) ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
        ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card = p + 1 ∧
      p * t ≤ s ^ 2 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, (span2 (residueAdj Δ P Q j k)
      ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card = p + 1 :=
    ⟨_ - 1, (Nat.sub_add_cancel (Finset.card_pos.2
      ⟨_, hO.toIsQuadrangle.left_mem_span2 _ _⟩)).symm⟩
  have hpq : Nat.card (P k) ≤ p := by
    have hsub := insert_image_conjSub_subset_lineOf hΔ (hF.memP j) (hF.memQ j)
    have hins := ncard_insert_image_conjSub hΔ (hF.memP j) (hF.memQ j) (hF.opposite j)
    have hline : (lineOf Δ (P j) (Q j)).ncard ≤
        (span2 (residueAdj Δ P Q j k)
          ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
          ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card :=
      hF.toIsFrame.ncard_lineOf_le_card_span2 j k
    have h2 : Nat.card (P j) + 1 ≤ p + 1 := by
      calc Nat.card (P j) + 1 =
          (insert (Q j) ((fun b => conjSub (P j) b) '' (Q j : Set H))).ncard := hins.symm
        _ ≤ (lineOf Δ (P j) (Q j)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (span2 (residueAdj Δ P Q j k)
            ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
            ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card := hline
        _ = p + 1 := hp
    have hcardP : Nat.card (P j) = Nat.card (P k) := hΔ.root.card_eq (hF.memP j) (hF.memP k)
    omega
  have hPQj : ¬ residueAdj Δ P Q j k
      ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩ :=
    ModelRank.not_commuting_of_opposite (hF.opposite j)
  exact ⟨p, hpq, hp, hO.mul_le_sq hs2 ht1 hPQj hp⟩

end

section Certificates


private theorem exists_order_data (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k)
    (hns : ¬ IsSmallFrame Δ P Q k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    ∃ s t, 2 ≤ s ∧ IsQuadrangleOfOrder (residueAdj Δ P Q j k) s t ∧
      t = Nat.card (P k) ^ 3 ∧ s ≤ Nat.card (P k) ^ 2 := by
  classical
  haveI : Finite H := h.finite
  have hΔ := h.cls
  have hthick := thickLines_of_meetsLines hΔ h.center hML
  letI : Nonempty ↥(rankTwoResidue Δ P Q j k) :=
    ⟨⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩⟩
  obtain ⟨s, t, hs2, -, hO⟩ :=
    (hF.isThickQuadrangle_residueAdj hΔ h.points hML hthick hjk).exists_order
  have hPjPk : (⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩ :
      ↥(rankTwoResidue Δ P Q j k)) ≠
      ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩ :=
    fun e => hF.toIsFrame.P_ne hjk (congrArg Subtype.val e)
  have hPQj : ¬ residueAdj Δ P Q j k
      ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩ :=
    ModelRank.not_commuting_of_opposite (hF.opposite j)
  have ht : t = Nat.card (P k) ^ 3 := by
    have h1 := hO.card_perp hPQj
    have h2 : (perp2 (residueAdj Δ P Q j k)
        ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
        ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card =
        Nat.card (P k) ^ 3 + 1 :=
      (hF.toIsFrame.card_perp2_residueAdj_PQ_left hjk).trans
        (hF.ncard_frameResidue_eq h hML hq hns)
    omega
  have hs : s ≤ Nat.card (P k) ^ 2 := by
    have hline := hO.card_line hPjPk (hF.toIsFrame.commuting_PP hjk)
    have hcard := hF.card_perp2_residueAdj_PP hΔ h.points hML hjk
    have hbound := hF.toIsFrame.ncard_lineOf_le_sq hΔ (hΔ.noIsolated h.points h.rank)
      h.points hML hthick hq hjk
    have hcardP : Nat.card (P j) = Nat.card (P k) := hΔ.root.card_eq (hF.memP j) (hF.memP k)
    have hcardP2 : Nat.card (P j) ^ 2 = Nat.card (P k) ^ 2 := by rw [hcardP]
    omega
  exact ⟨s, t, hs2, hO, ht, hs⟩

private theorem order_and_span (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k)
    (hns : ¬ IsSmallFrame Δ P Q k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    IsQuadrangleOfOrder (residueAdj Δ P Q j k) (Nat.card (P k) ^ 2) (Nat.card (P k) ^ 3) ∧
      (span2 (residueAdj Δ P Q j k) ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
        ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card = Nat.card (P k) + 1 := by
  classical
  haveI : Finite H := h.finite
  obtain ⟨s, t, hs2, hO, ht, hs⟩ := exists_order_data h hML hq hF hjk hns
  have ht1 : 1 ≤ t := by
    rw [ht]
    exact Nat.succ_le_of_lt (pow_pos (by have := hq _ (hF.memP k); omega) 3)
  obtain ⟨p, hpq, hp, hthas⟩ := exists_span_data h.cls hF hO hs2 ht1
  have hlow : Nat.card (P k) ^ 4 ≤ s ^ 2 := by
    have hle : Nat.card (P k) * t ≤ p * t := Nat.mul_le_mul_right t hpq
    rw [ht] at hle
    calc Nat.card (P k) ^ 4 = Nat.card (P k) * Nat.card (P k) ^ 3 := by ring
      _ ≤ p * Nat.card (P k) ^ 3 := hle
      _ ≤ s ^ 2 := by rw [← ht]; exact hthas
  have hhigh : s ^ 2 ≤ Nat.card (P k) ^ 4 := by
    calc s ^ 2 ≤ (Nat.card (P k) ^ 2) ^ 2 := Nat.pow_le_pow_left hs 2
      _ = Nat.card (P k) ^ 4 := by ring
  have hsq : s ^ 2 = Nat.card (P k) ^ 4 := le_antisymm hhigh hlow
  have hs_eq : s = Nat.card (P k) ^ 2 := by
    refine Nat.mul_self_inj.1 ?_
    simpa only [pow_two] using hsq.trans (by ring)
  have hpt : p * t = Nat.card (P k) ^ 4 := by
    have h1 : Nat.card (P k) ^ 4 ≤ p * t := by
      calc Nat.card (P k) ^ 4 = Nat.card (P k) * Nat.card (P k) ^ 3 := by ring
        _ ≤ p * Nat.card (P k) ^ 3 := Nat.mul_le_mul_right _ hpq
        _ = p * t := by rw [ht]
    exact le_antisymm (hthas.trans hhigh) h1
  have hp_eq : p = Nat.card (P k) := by
    have hq0 : 0 < Nat.card (P k) := by
      have := hq _ (hF.memP k)
      omega
    have hcancel : p * Nat.card (P k) ^ 3 = Nat.card (P k) * Nat.card (P k) ^ 3 := by
      calc p * Nat.card (P k) ^ 3 = p * t := by rw [ht]
        _ = Nat.card (P k) ^ 4 := hpt
        _ = Nat.card (P k) * Nat.card (P k) ^ 3 := by ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 3) hcancel
  exact ⟨by simpa [hs_eq, ht] using hO, by rw [hp, hp_eq]⟩

theorem IsMaxFrame.not_isSmallFrame_of_ne (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k)
    (hns : ¬ IsSmallFrame Δ P Q j) : ¬ IsSmallFrame Δ P Q k := by
  classical
  haveI : Finite H := h.finite
  intro hs
  have hthick := thickLines_of_meetsLines h.cls h.center hML
  have hsub : frameResidue Δ P Q k ⊆
      insert (Q k) ((fun b => conjSub (P k) b) '' (Q k : Set H)) :=
    fun X hX => mem_insert_image_conjSub_of_le h.cls (hF.memQ k) (hF.opposite k) hX.1
      (hs.residue X hX.1 hX.2)
  have hsmall : (frameResidue Δ P Q k).ncard ≤ Nat.card (P k) + 1 := by
    calc (frameResidue Δ P Q k).ncard
        ≤ (insert (Q k) ((fun b => conjSub (P k) b) '' (Q k : Set H))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (P k) + 1 :=
          ncard_insert_image_conjSub h.cls (hF.memP k) (hF.memQ k) (hF.opposite k)
  have hcard := hF.ncard_frameResidue_eq_of_ne h.cls h.points hML hthick hjk
  have hbig := hF.ncard_frameResidue_eq h hML hq hns
  have hcardP : Nat.card (P j) = Nat.card (P k) := h.cls.root.card_eq (hF.memP j) (hF.memP k)
  have hbig' : (frameResidue Δ P Q k).ncard = Nat.card (P k) ^ 3 + 1 := by
    rw [← hcard, hbig, hcardP]
  have hineq : Nat.card (P k) ^ 3 + 1 ≤ Nat.card (P k) + 1 := by
    rw [← hbig']
    exact hsmall
  have h4 : 4 ≤ Nat.card (P k) := hq _ (hF.memP k)
  have hlt : Nat.card (P k) + 1 < Nat.card (P k) ^ 3 + 1 := by
    have hprod : Nat.card (P k) * 4 ^ 2 ≤ Nat.card (P k) * Nat.card (P k) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 2)
    have hcube : Nat.card (P k) ^ 3 = Nat.card (P k) * Nat.card (P k) ^ 2 := by ring
    rw [hcube]
    nlinarith [hprod, h4]
  exact (not_le_of_gt hlt) hineq

theorem IsMaxFrame.isQuadrangleOfOrder_residueAdj (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) (hns : ¬ IsSmallFrame Δ P Q k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    IsQuadrangleOfOrder (residueAdj Δ P Q j k) (Nat.card (P k) ^ 2) (Nat.card (P k) ^ 3) :=
  (order_and_span h hML hq hF hjk hns).1

theorem IsMaxFrame.card_span2_residueAdj (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k)
    (hns : ¬ IsSmallFrame Δ P Q k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    (span2 (residueAdj Δ P Q j k) ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card = Nat.card (P k) + 1 :=
  (order_and_span h hML hq hF hjk hns).2

theorem IsMaxFrame.image_span2_residueAdj_eq_lineOf (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) (hns : ¬ IsSmallFrame Δ P Q k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    Subtype.val '' (↑(span2 (residueAdj Δ P Q j k) ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩) : Set ↥(rankTwoResidue Δ P Q j k)) =
      lineOf Δ (P j) (Q j) := by
  classical
  haveI : Finite H := h.finite
  have hspan := (order_and_span h hML hq hF hjk hns).2
  have hsub := IsFrame.lineOf_subset_image_span2 hF.toIsFrame j k
  have himg : (Subtype.val '' (↑(span2 (residueAdj Δ P Q j k)
        ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
        ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩) :
          Set ↥(rankTwoResidue Δ P Q j k))).ncard =
      (span2 (residueAdj Δ P Q j k)
        ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
        ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card := by
    rw [Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]
  have hcardP : Nat.card (P j) = Nat.card (P k) := h.cls.root.card_eq (hF.memP j) (hF.memP k)
  have hline : Nat.card (P j) + 1 ≤ (lineOf Δ (P j) (Q j)).ncard := by
    calc Nat.card (P j) + 1 =
        (insert (Q j) ((fun b => conjSub (P j) b) '' (Q j : Set H))).ncard :=
          (ncard_insert_image_conjSub h.cls (hF.memP j) (hF.memQ j) (hF.opposite j)).symm
      _ ≤ (lineOf Δ (P j) (Q j)).ncard :=
          Set.ncard_le_ncard (insert_image_conjSub_subset_lineOf h.cls (hF.memP j) (hF.memQ j))
            (Set.toFinite _)
  exact (Set.eq_of_subset_of_ncard_le hsub
    (by rw [himg, hspan, ← hcardP]; exact hline) (Set.toFinite _)).symm

theorem IsMaxFrame.ncard_lineOf_eq_of_mem_rankTwoResidue (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) (hns : ¬ IsSmallFrame Δ P Q k) {X Y : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) (hY : Y ∈ rankTwoResidue Δ P Q j k) (hXY : X ≠ Y)
    (hc : Commuting X Y) : (lineOf Δ X Y).ncard = Nat.card (P k) ^ 2 + 1 := by
  classical
  haveI : Finite H := h.finite
  letI : Fintype ↥(rankTwoResidue Δ P Q j k) := Fintype.ofFinite _
  have hXY' : (⟨X, hX⟩ : ↥(rankTwoResidue Δ P Q j k)) ≠ ⟨Y, hY⟩ :=
    fun e => hXY (congrArg Subtype.val e)
  rw [← hF.image_perp2_residueAdj_eq_lineOf h.cls h.points hML hX hY hXY hc,
    Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]
  exact (order_and_span h hML hq hF hjk hns).1.card_line hXY' hc

end Certificates

end CFSG.Timmesfeld.Transvection
