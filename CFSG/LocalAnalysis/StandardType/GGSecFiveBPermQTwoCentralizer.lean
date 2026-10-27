module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBlockCentralizer
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.CALinearPlane

open Matrix Subgroup CFSG.SeitzReduction.LinearPilot

variable {n : ℕ} {F : Type*} [Field F]

private theorem coordBlockSL_eq_blockSpecialLinear (S : Finset (Fin n)) :
    coordBlockSL F S = blockSpecialLinear (K := F) S := by
  ext g
  rw [mem_coordBlockSL_iff, mem_blockSpecialLinear]
  simp only [Matrix.one_apply]

theorem coordBlockSL_inf (I J : Finset (Fin n)) :
    coordBlockSL F I ⊓ coordBlockSL F J = coordBlockSL F (I ∩ J) := by
  rw [coordBlockSL_eq_blockSpecialLinear I, coordBlockSL_eq_blockSpecialLinear J,
    coordBlockSL_eq_blockSpecialLinear (I ∩ J)]
  exact blockSpecialLinear_inf I J

theorem coordBlockSL_map_inf_centralizer_eq_sdiff {G : Type*} [Group G]
    (κ : SpecialLinearGroup (Fin n) F →* G) (hκ : Function.Injective κ)
    (I J : Finset (Fin n)) (hJ : 2 ≤ J.card) (hJI : ∃ d ∈ J, d ∉ I) :
    (coordBlockSL F I).map κ ⊓ centralizer ((coordBlockSL F J).map κ : Set G) =
      (coordBlockSL F (I \ J)).map κ := by
  rw [coordBlockSL_eq_blockSpecialLinear I, coordBlockSL_eq_blockSpecialLinear J,
    coordBlockSL_eq_blockSpecialLinear (I \ J)]
  exact blockSpecialLinear_map_inf_centralizer_eq_sdiff κ hκ I J hJ hJI

theorem coordBlockSL_map_inf_centralizer_eq_sdiff_of_card_two [Finite F]
    (hF : Nat.card F = 2) {G : Type*} [Group G]
    (κ : SpecialLinearGroup (Fin n) F →* G) (hκ : Function.Injective κ)
    (I J : Finset (Fin n)) (hJ : 2 ≤ J.card) :
    (coordBlockSL F I).map κ ⊓ centralizer ((coordBlockSL F J).map κ : Set G) =
      (coordBlockSL F (I \ J)).map κ := by
  rw [coordBlockSL_eq_blockSpecialLinear I, coordBlockSL_eq_blockSpecialLinear J,
    coordBlockSL_eq_blockSpecialLinear (I \ J)]
  exact blockSpecialLinear_map_inf_centralizer_eq_sdiff_of_card_two hF κ hκ I J hJ

end CFSG.RankThree.CALinearPlane

end
