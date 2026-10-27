module

public import CFSG.RankThree.PartTwo.KFacts.KP4Signal

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.M22

open Subgroup CFSG.RankThree.PartTwo.KFacts.KP4
open CFSG.RankThree.Asc83Table.M22 (X Y)


@[expose] def sg : List G22 := [X, Y, vAE 0, vBE 0]

theorem closure_sg : closure {g | g ∈ sg} = P0 ⊔ V 0 := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [sg, List.mem_cons, List.mem_nil_iff, or_false, Set.mem_setOf_eq] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left X_mem_P0
    · exact mem_sup_left Y_mem_P0
    · exact mem_sup_right (by rw [← V_eq_closure]; exact subset_closure (Set.mem_insert _ _))
    · exact mem_sup_right (by rw [← V_eq_closure]; exact subset_closure (Set.mem_insert_of_mem _ rfl))
  · refine sup_le ?_ ?_
    · change closure ({X, Y} : Set G22) ≤ _
      exact closure_mono (by intro g hg; rcases hg with rfl | rfl <;> simp [sg])
    · rw [← V_eq_closure]
      exact closure_mono (by intro g hg; rcases hg with rfl | rfl <;> simp [sg])

theorem card_P0_sup_V :
    Nat.card (P0 ⊔ V 0 : Subgroup G22) = 36 := by
  have hle : P0 ⊔ V 0 ≤ centralizer ({lineE 0} : Set G22) :=
    sup_le (P0_le_centralizer 0) (V_le_centralizer 0)
  have h1 : Nat.card (P0 ⊔ V 0 : Subgroup G22) ≤ 36 := by
    rw [← card_centralizer_line 0]
    exact Subgroup.card_le_of_le hle
  have h9 : 9 ∣ Nat.card (P0 ⊔ V 0 : Subgroup G22) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : P0 ≤ P0 ⊔ V 0)
    rwa [card_P0] at this
  have h4 : 4 ∣ Nat.card (P0 ⊔ V 0 : Subgroup G22) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : V 0 ≤ P0 ⊔ V 0)
    rwa [card_V] at this
  have h36 : 36 ∣ Nat.card (P0 ⊔ V 0 : Subgroup G22) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h4
  have hpos : 0 < Nat.card (P0 ⊔ V 0 : Subgroup G22) := Nat.card_pos
  have := Nat.le_of_dvd hpos h36
  omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.M22

end
