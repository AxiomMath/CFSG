module

public import CFSG.Timmesfeld.Transvection.ResidueBender
import CFSG.Timmesfeld.Transvection.Small
import CFSG.Timmesfeld.Transvection.FrameThrough
import CFSG.Timmesfeld.Transvection.LineConjugates
import CFSG.Timmesfeld.Transvection.FrameLineCard
import CFSG.Timmesfeld.Transvection.ResidueQuadrangle
import CFSG.Combinatorics.QuadrangleGraphOrder
import CFSG.Combinatorics.QuadrangleGraphThas

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Combinatorics.QuadrangleGraph

variable {H : Type} [Group H] {Δ : Set (Subgroup H)}

private theorem le_of_mul_cube_le {p q s t : ℕ} (hq : 0 < q) (ht : t = q ^ 3) (hs : s ≤ q ^ 2)
    (h : p * t ≤ s ^ 2) : p ≤ q :=
  Nat.le_of_mul_le_mul_right (calc
      p * q ^ 3 = p * t := by rw [ht]
      _ ≤ s ^ 2 := h
      _ ≤ (q ^ 2) ^ 2 := Nat.pow_le_pow_left hs 2
      _ = q * q ^ 3 := by ring) (pow_pos hq 3)

section HyperbolicLine


theorem IsMaxFrame.lineOf_eq_of_not_isSmallFrame (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) {r : ℕ} {P Q : Fin r → Subgroup H}
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k) (hns : ¬ IsSmallFrame Δ P Q j) :
    lineOf Δ (P j) (Q j) = insert (Q j) ((fun b => conjSub (P j) b) '' (Q j : Set H)) := by
  classical
  haveI : Finite H := h.finite
  have hΔ := h.cls
  have hiso : NoIsolated Δ := hΔ.noIsolated h.points h.rank
  have hthick := thickLines_of_meetsLines hΔ h.center hML
  letI : Fintype ↥(rankTwoResidue Δ P Q j k) := Fintype.ofFinite _
  haveI : Nonempty ↥(rankTwoResidue Δ P Q j k) :=
    ⟨⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩⟩
  obtain ⟨s, t, hs2, ht2, hO⟩ :=
    (hF.isThickQuadrangle_residueAdj hΔ h.points hML hthick hjk).exists_order
  have hPQk : ¬ residueAdj Δ P Q j k ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩
      ⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_right j k⟩ :=
    ModelRank.not_commuting_of_opposite (hF.opposite k)
  have ht : t = Nat.card (P j) ^ 3 :=
    Nat.add_right_cancel ((hO.card_perp hPQk).symm.trans
      ((hF.toIsFrame.card_perp2_residueAdj_PQ hjk).trans
        (hF.ncard_frameResidue_eq h hML hq hns)))
  have hPjPk : (⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩ :
      ↥(rankTwoResidue Δ P Q j k)) ≠
      ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩ :=
    fun e => hF.toIsFrame.P_ne hjk (congrArg Subtype.val e)
  have hline : (perp2 (residueAdj Δ P Q j k)
      ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩).card = s + 1 :=
    hO.card_line hPjPk (hF.toIsFrame.commuting_PP hjk)
  have hline' : (perp2 (residueAdj Δ P Q j k)
      ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩).card =
      (lineOf Δ (P j) (P k)).ncard :=
    hF.card_perp2_residueAdj_PP hΔ h.points hML hjk
  have hbound := hF.toIsFrame.ncard_lineOf_le_sq hΔ hiso h.points hML hthick hq hjk
  have hs : s ≤ Nat.card (P j) ^ 2 := by omega
  obtain ⟨p, hp⟩ : ∃ p, (span2 (residueAdj Δ P Q j k)
      ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card = p + 1 :=
    ⟨_ - 1, (Nat.sub_add_cancel (Finset.card_pos.2
      ⟨_, hO.toIsQuadrangle.left_mem_span2 _ _⟩)).symm⟩
  have hPQj : ¬ residueAdj Δ P Q j k ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩ :=
    ModelRank.not_commuting_of_opposite (hF.opposite j)
  have hThas := hO.mul_le_sq hs2 (by omega) hPQj hp
  have hpq : p ≤ Nat.card (P j) :=
    le_of_mul_cube_le (by have := hq _ (hF.memP j); omega) ht hs hThas
  refine lineOf_eq_insert_of_ncard_le hΔ (hF.memP j) (hF.memQ j) (hF.opposite j) ?_
  calc (lineOf Δ (P j) (Q j)).ncard
      ≤ (span2 (residueAdj Δ P Q j k)
          ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
          ⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩).card :=
        hF.toIsFrame.ncard_lineOf_le_card_span2 j k
    _ = p + 1 := hp
    _ ≤ Nat.card (P j) + 1 := Nat.add_le_add_right hpq 1

theorem lineOf_eq_of_opposite (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) {A B : Subgroup H} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hAB : Opposite A B) :
    lineOf Δ A B = insert B ((fun b => conjSub A b) '' (B : Set H)) ∧
      ∀ Y ∈ lineOf Δ A B, Y ≤ A ⊔ B := by
  haveI : Finite H := h.finite
  obtain ⟨n, hn, P, Q, hF, hPA, hQB⟩ := exists_isMaxFrame_last h hML hA hB hAB
  have hjk : Fin.last n ≠ (0 : Fin (n + 1)) :=
    Fin.ne_of_val_ne (by rw [Fin.val_last, Fin.val_zero]; omega)
  rw [← hPA, ← hQB]
  by_cases hs : IsSmallFrame Δ P Q (Fin.last n)
  · exact hs.lineOf_eq h.cls
  · have heq := hF.lineOf_eq_of_not_isSmallFrame h hML hq hjk hs
    exact ⟨heq, fun Y hY => by
      rw [heq] at hY
      exact le_sup_of_mem_insert_image_conjSub hY⟩

end HyperbolicLine

end CFSG.Timmesfeld.Transvection