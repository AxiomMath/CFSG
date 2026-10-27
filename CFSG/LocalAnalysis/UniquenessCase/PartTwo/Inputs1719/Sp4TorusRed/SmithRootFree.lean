module

public import CFSG.RankThree.GF2n.Smith81.Lin22SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n.Smith81.SL2Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem le_normalizer_torus_of_inf_eq_bot (h4 : 4 ≤ Nat.card F) {N : Subgroup SL(2, F)}
    (hT : torus F ≤ N) (hU : N ⊓ utri F = ⊥) (hL : N ⊓ ltri F = ⊥) :
    N ≤ Subgroup.normalizer (torus F : Set SL(2, F)) := by
  have hno := not_exists_conjSubgroup_utri_ne_utri_ne_ltri h4 hT hU hL
  intro n hnN
  by_cases hnU : conjSubgroup n (utri F) = utri F
  · have hnNorm : n ∈ Subgroup.normalizer (utri F : Set SL(2, F)) :=
      mem_normalizer_iff_conjSubgroup_eq.2 hnU
    have hnB : n ∈ borel F := by
      rw [← normalizer_utri]
      exact hnNorm
    have hmem : n ∈ N ⊓ borel F := ⟨hnN, hnB⟩
    rw [inf_borel_eq_torus hT hU] at hmem
    exact Subgroup.le_normalizer hmem
  · have hnL : conjSubgroup n (utri F) = ltri F := by
      by_contra hnL
      exact hno ⟨n, hnN, hnU, hnL⟩
    exact mem_normalizer_torus_of_conjSubgroup_utri_eq_ltri hT hL hnN hnL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
