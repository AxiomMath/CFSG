module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Par
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Levi

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem inf_M_eq_of_l3 (hirr : SL3OddIrr) (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] {K T M : Subgroup X} (hX : ASHyp K T M)
    (e : ↥K ≃* PSL3 p) :
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) ∧ ¬ T ≤ K := by
  obtain ⟨U, c, d, hU, hUB, hQ, hc, hd⟩ := exists_special_sylow hp2
  have hB := centralizer_zOf_eq_leviC hp2 hU hUB
  refine hX.inf_M_eq_of_levi_pair e hU (P₁ := lineC p) (P₂ := planeC p) ?_ ?_ lineC_ne_planeC
    lineC_ne_top planeC_ne_top card_lineC_eq_planeC (lineC_sup_planeC hirr hp2) ?_ ?_ ?_
  · rw [hB]
    exact leviC_le_lineC
  · rw [hB]
    exact leviC_le_planeC
  · intro Y hBY hY
    rw [hB] at hBY
    exact le_parabolics_of_le_levi hirr hp2 hBY hY
  · intro Y hBY hY
    rw [hB] at hBY ⊢
    exact eq_levi_or_eq_lineC hBY hY
  · intro Y hBY hY
    rw [hB] at hBY ⊢
    exact eq_levi_or_eq_planeC hBY hY

end CFSG.Quasithin.E2P.Asc80
