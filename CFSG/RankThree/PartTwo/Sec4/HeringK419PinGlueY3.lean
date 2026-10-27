module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinGlueY2
public import CFSG.RankThree.PartTwo.Sec4.Item413Orders

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.RankThree.PartTwo.Sec6.BThreeCensus

theorem num_c7 {X : Type} [Group X]
    (h : Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 2)) :
    NumList46 (Nat.card X) := by
  refine NumList46.explicit ?_
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    refine ⟨9999360, by decide +kernel, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    refine (card_projSL_dvd 5 (GaloisField 2 1)).trans ?_
    rw [card_SL_galoisField 5 2 1 one_ne_zero]
    decide
  · obtain ⟨e⟩ := h
    refine ⟨1451520, by decide +kernel, ?_⟩
    rw [Nat.card_congr e.toEquiv, card_projSp_three_two]
  · obtain ⟨e⟩ := h
    refine ⟨4 ^ 10 * 254840625, by decide +kernel, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    exact card_projSU_five_four_dvd

section Certs


theorem num_c8 {X : Type} [Group X] [Finite X]
    (h : (∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
        (Nonempty (X ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (X ≃* projSU 3 3 e))) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      (Nat.card (Subgroup.center X) ≤ 3 ∧
        (ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
          Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)))) : NumList46 (Nat.card X) := by
  refine NumList46.explicit ?_
  rcases h with ⟨e, he1, he2, h⟩ | h | ⟨hZ, h⟩
  · rcases h with h | h
    · obtain ⟨f⟩ := h
      interval_cases e
      · refine ⟨5616, by decide +kernel, ?_⟩
        rw [Nat.card_congr f.toEquiv]
        refine (card_projSL_dvd 3 (GaloisField 3 1)).trans ?_
        rw [card_SL_galoisField 3 3 1 one_ne_zero]
        decide
      · refine ⟨42456960, by decide +kernel, ?_⟩
        rw [Nat.card_congr f.toEquiv]
        refine (card_projSL_dvd 3 (GaloisField 3 2)).trans ?_
        rw [card_SL_galoisField 3 3 2 two_ne_zero]
        decide
    · obtain ⟨f⟩ := h
      interval_cases e
      · refine ⟨6048, by decide +kernel, ?_⟩
        rw [Nat.card_congr f.toEquiv]
        exact (card_projSU_three_three_dvd le_rfl).trans (by decide)
      · refine ⟨42573600, by decide +kernel, ?_⟩
        rw [Nat.card_congr f.toEquiv]
        exact (card_projSU_three_three_dvd (by norm_num)).trans (by decide)
  · obtain ⟨f⟩ := h
    refine ⟨12130560, by decide +kernel, ?_⟩
    rw [Nat.card_congr f.toEquiv]
    refine (card_projSL_dvd 4 (GaloisField 3 1)).trans ?_
    rw [card_SL_galoisField 4 3 1 one_ne_zero]
    decide
  · have hpos : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
    rw [card_eq_card_center_mul]
    rcases h with hG | h
    · have h1 : Nat.card (X ⧸ Subgroup.center X) = 4245696 := by
        rw [(CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG).1 rfl]
        decide
      refine ⟨25474176, by decide +kernel, ?_⟩
      rw [h1]
      generalize Nat.card (Subgroup.center X) = z at *
      interval_cases z <;> decide
    · obtain ⟨f⟩ := h
      refine ⟨19595520, by decide +kernel, ?_⟩
      rw [Nat.card_congr f.toEquiv, card_projSU_four_three]
      generalize Nat.card (Subgroup.center X) = z at *
      interval_cases z <;> decide

end Certs

theorem numList46_of_isList46 {X : Type} [Group X] [Finite X]
    (h : IsList46 X) : NumList46 (Nat.card X) := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact num_c1 h1
  · exact num_c2 h2
  · exact num_c3 h3
  · exact num_c4 h4
  · exact num_c5 h5
  · exact num_c6 h6
  · exact num_c7 h7
  · exact num_c8 h8

end CFSG.RankThree.PartTwo.Sec4.HeringPin
