module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row6
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row8
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Exists
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open

theorem rowLeaves_psl_four_four {K : Type} [Group K] [Finite K] (h : LieModel K .PSL 4 2 2) :
    RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨ω, hω⟩ := exists_omega_of_three_dvd (F := F) (by omega)
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row1_elements hω
  have hbot : (StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F) = ⊥ :=
    statedScalars_subgroupOf_statedSL_eq_bot fun c hc h4 =>
      eq_one_of_pow_eq_one_of_coprime (by rw [hF]; decide) hc h4
  exact rowLeaves_of_statedProj hbot e (row1_holds F hF ω hω z₀ t₀ hz ht)

theorem rowLeaves_psp_three_four {K : Type} [Group K] [Finite K] (h : LieModel K .PSp 3 2 2) :
    RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have : CharP F 2 := charP_of_nat_card_eq hcard
  obtain ⟨ω, hω⟩ := exists_omega_of_three_dvd (F := F) (by omega)
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row2_elements hω
  exact rowLeaves_of_statedProj StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot e
    (row2_holds F hF ω hω z₀ t₀ hz ht)

theorem rowLeaves_pOmegaMinus_four_four {K : Type} [Group K] [Finite K]
    (h : LieModel K .POmegaMinus 4 2 2) : RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, b, c, hbc, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have : CharP F 2 := charP_of_nat_card_eq hcard
  obtain ⟨ω, hω⟩ := exists_omega_of_three_dvd (F := F) (by omega)
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row3_elements hω
  exact rowLeaves_of_matrixRowData
    (e.trans (CFSG.AGLEmbedding.LeviBlock.orthMinusStatedProjEquiv (by norm_num)))
    (row3_holds F hF b c hbc ω hω z₀ t₀ hz ht)

theorem rowLeaves_psl_six_two {K : Type} [Group K] [Finite K] (h : LieModel K .PSL 6 2 1) :
    RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row4_elements (F := F)
  have hbot : (StatedScalars (Fin 6) F).subgroupOf (StatedSL 6 F) = ⊥ :=
    statedScalars_subgroupOf_statedSL_eq_bot fun c hc h6 =>
      eq_one_of_pow_eq_one_of_coprime (by rw [hF]; decide) hc h6
  exact rowLeaves_of_statedProj hbot e (row4_holds F hF z₀ t₀ hz ht)

theorem rowLeaves_psl_seven_two {K : Type} [Group K] [Finite K] (h : LieModel K .PSL 7 2 1) :
    RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row5_elements (F := F)
  have hbot : (StatedScalars (Fin 7) F).subgroupOf (StatedSL 7 F) = ⊥ :=
    statedScalars_subgroupOf_statedSL_eq_bot fun c hc h7 =>
      eq_one_of_pow_eq_one_of_coprime (by rw [hF]; decide) hc h7
  exact rowLeaves_of_statedProj hbot e (row5_holds F hF z₀ t₀ hz ht)

theorem rowLeaves_psu_four_eight {K : Type} [Group K] [Finite K] (h : LieModel K .PSU 4 2 3) :
    RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 64 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨ω, hω⟩ := exists_omega_of_three_dvd (F := F) (by omega)
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row1_elements hω
  have hbot : (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (2 ^ 3) F) = ⊥ :=
    statedScalars_subgroupOf_statedSU_eq_bot fun c hc h4 =>
      eq_one_of_pow_eq_one_of_coprime (by rw [hF]; decide) hc h4
  exact rowLeaves_of_statedProj hbot e (row6_holds F hF ω hω z₀ t₀ hz ht)

theorem rowLeaves_psp_three_eight {K : Type} [Group K] [Finite K] (h : LieModel K .PSp 3 2 3) :
    RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 8 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have : CharP F 2 := charP_of_nat_card_eq hcard
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row7_elements (F := F)
  exact rowLeaves_of_statedProj StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot e
    (row7_holds F hF z₀ t₀ hz ht)

theorem rowLeaves_pOmegaMinus_four_eight {K : Type} [Group K] [Finite K]
    (h : LieModel K .POmegaMinus 4 2 3) : RowLeaves K := by
  obtain ⟨-, F, _, _, hcard, b, c, hbc, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Fintype F := Fintype.ofFinite F
  let : DecidableEq F := Classical.decEq F
  have hF : Fintype.card F = 8 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have : CharP F 2 := charP_of_nat_card_eq hcard
  obtain ⟨α, hα⟩ := exists_alpha_of_irreducible hF b c hbc
  obtain ⟨z₀, t₀, hz, ht⟩ := exists_row8_elements b c hbc α hα
  exact rowLeaves_of_matrixRowData
    (e.trans (CFSG.AGLEmbedding.LeviBlock.orthMinusStatedProjEquiv (by norm_num)))
    (row8_holds F hF b c hbc α hα z₀ t₀ hz ht)

theorem classicalRows_holds :
    ∀ (K : Type) [Group K] [Finite K],
      (LieModel K .PSL 4 2 2 ∨ LieModel K .PSp 3 2 2 ∨ LieModel K .POmegaMinus 4 2 2 ∨
        LieModel K .PSL 6 2 1 ∨ LieModel K .PSL 7 2 1 ∨ LieModel K .PSU 4 2 3 ∨
        LieModel K .PSp 3 2 3 ∨ LieModel K .POmegaMinus 4 2 3) → RowLeaves K := by
  intro K _ _ h
  rcases h with h | h | h | h | h | h | h | h
  · exact rowLeaves_psl_four_four h
  · exact rowLeaves_psp_three_four h
  · exact rowLeaves_pOmegaMinus_four_four h
  · exact rowLeaves_psl_six_two h
  · exact rowLeaves_psl_seven_two h
  · exact rowLeaves_psu_four_eight h
  · exact rowLeaves_psp_three_eight h
  · exact rowLeaves_pOmegaMinus_four_eight h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
