module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.Adapters.LieModelSmallOrders
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row4.Pos

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

private theorem k328r4s_card_gl (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 2) :
    Nat.card (GL (Fin 6) F) = 20158709760 := by
  rw [Matrix.card_GL_field, hF, Fin.prod_univ_six]
  norm_num

private theorem k328r4s_card_pos {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (h : Pos K Z X) : Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
  obtain ⟨-, -, -, -, -, hZ, hL⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X), hZ]
  rcases hL with h | h
  · left
    rw [CFSG.Blueprint.LieModel.card_psl_three_four h]
  · right
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (h.statedClassicalModel (by decide))]

private theorem k328r4s_card_of_pos {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) {Z : Subgroup ↥(StatedSL 6 F)} {Y : Subgroup (GL (Fin 6) F)}
    (hY : Y ≤ StatedSL 6 F) (h : Pos ↥(StatedSL 6 F) Z (Y.subgroupOf (StatedSL 6 F))) :
    Nat.card Y = 60480 := by
  have hc : Nat.card Y = 60480 ∨ Nat.card Y = 16547328 := by
    rw [← card_subgroupOf_of_le hY]
    exact k328r4s_card_pos h
  have hd : Nat.card Y ∣ 20158709760 := by
    rw [← k328r4s_card_gl F hF]
    exact Subgroup.card_subgroup_dvd_card Y
  rcases hc with hc | hc
  · exact hc
  · rw [hc] at hd
    exact absurd hd (by norm_num)

theorem row4_size (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ t₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (ht : (t₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    SizeLeaf (StatedSL 6 F) z₀ := by
  intro hz₀ X hX hP
  have hS := row4_pos F hF z₀ t₀ hz ht hz₀
  rw [k328r4s_card_of_pos hF (hX.trans (stdComp_le _ _)) hP,
    k328r4s_card_of_pos hF (stdComp_le _ _) hS]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
