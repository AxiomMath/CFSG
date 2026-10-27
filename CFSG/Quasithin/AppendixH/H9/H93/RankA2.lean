module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitA2
public import CFSG.Quasithin.AppendixH.H9.H93.RankA2.Coordinates
public import CFSG.Quasithin.AppendixH.H9.H93.RankA2.FixedPoints

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open
open A2Coords

theorem rank_A2g :
    ∀ a ∈ A2g, a ∉ Lg 4 →
      ((fixV A2g : Subgroup (PairN 4)) : Set (PairN 4)) =
          {x | ∃ w ∈ V1n 4 ⊓ fixV (A2g ⊓ Lg 4), x = w * a w} ∧
        rk ↥(fixV A2g) = 2 ∧
        E3.gammaCheck 2 A2g = fixV (A2g ⊓ Lg 4) ⊔ fixV (Subgroup.zpowers a) ∧
        rk ↥(E3.gammaCheck 2 A2g) = 6 := by
  obtain ⟨ρ, hinj, hrange, hact, hL⟩ := exists_param_A2g
  intro a ha haL
  rw [← hrange] at ha ⊢
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨ε₁, rfl⟩ := Multiplicative.ofAdd.surjective m
  have h3 : ε₁ 3 = 1 := A2_eps3_eq_one_of_ne_zero ε₁ fun h => haL ((hL ε₁).2 h)
  refine ⟨fixV_range_set_eq hact hL h3, ?_, gammaCheck_two_range_eq_sup hinj hact hL h3, ?_⟩
  · refine rk_eq_of_card_eq_two_pow _ 2 ?_
    exact (card_eq_fintype_card_of_pairVec_mem_iff _
      (fun p => A2Fixed p.1 ∧ p.1 = p.2) (pairVec_mem_fixV_range_iff hact)).trans
        card_A2_diagonal
  · rw [gammaCheck_two_range_eq_sup hinj hact hL h3]
    refine rk_eq_of_card_eq_two_pow _ 6 ?_
    exact (card_eq_fintype_card_of_pairVec_mem_iff _
      (fun p => A2Fixed (p.1 + A2vec ε₁ p.2)) (pairVec_mem_sup_iff hact hL h3)).trans
        (card_A2_radical ε₁ h3)

end CFSG.ASVolI.ChH
