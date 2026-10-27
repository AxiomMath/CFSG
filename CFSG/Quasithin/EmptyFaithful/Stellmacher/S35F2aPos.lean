module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aOrb
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aP10
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aThat

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2a

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]

theorem index_of_card_twelve {K : Subgroup (Perm (Fin 5))} (h : Nat.card K = 12) :
    K.index = 10 := by
  have := Subgroup.card_mul_index K
  rw [h, card_perm_five] at this
  omega

private theorem fixPt_conj0 (g : Perm (Fin 5)) : fixPt (cj g S5Syl) = g 4 := by
  rw [fixPt_cj card_S5Syl, fixPt_std]

private theorem fixPt_conj (g r : Perm (Fin 5)) : fixPt (cj g (cj r S5Syl)) = g (r 4) := by
  rw [fixPt_cj (card_cj_S5Syl r), fixPt_cj card_S5Syl, fixPt_std]

theorem r2_fix : r2 4 = 4 := by unfold r2; decide +kernel
theorem r4_move : r4 4 ≠ 4 := by unfold r4; decide +kernel
theorem r8_move : r8 4 ≠ 4 := by unfold r8; decide +kernel
theorem r2_not_mem : r2 ∉ S5Syl := by
  rw [mem_S5Syl_iff]; unfold r2 S5SylF; decide +kernel

private theorem sup_conj (g : Perm (Fin 5)) (F : Subgroup (Perm (Fin 5))) :
    That (cj g S5Syl) ⊔ That (cj g F) = cj g (That S5Syl ⊔ That F) := by
  rw [← cj_That, ← cj_That, ← cj_sup]

theorem sylPair_position {D E : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hE : Nat.card E = 8) :
    (D = E ∧ suborbitSize D E = 1) ∨
    (D ≠ E ∧ fixPt D = fixPt E ∧ suborbitSize D E = 2 ∧ D ⊔ E = ptStab (fixPt D) ∧
      That D ⊔ That E = ptStab (fixPt D)) ∨
    (fixPt D ≠ fixPt E ∧ suborbitSize D E = 4 ∧ D ⊔ E = ⊤ ∧
      Nat.card ↥(That D ⊔ That E) = 12) ∨
    (fixPt D ≠ fixPt E ∧ suborbitSize D E = 8 ∧ D ⊔ E = ⊤ ∧ That D ⊔ That E = ⊤) := by
  obtain ⟨g, rfl, h⟩ := sylPair_cases hD hE
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, by rw [suborbitSize_cj]; exact suborbitSize_std_self⟩
  · have hne : cj g S5Syl ≠ cj g (cj r2 S5Syl) := fun h =>
      r2_not_mem (cj_S5Syl_eq_iff.mp (cj_injective g h).symm)
    have hfp : fixPt (cj g S5Syl) = fixPt (cj g (cj r2 S5Syl)) := by
      rw [fixPt_conj0, fixPt_conj, r2_fix]
    refine Or.inr (Or.inl ⟨hne, hfp, ?_, sup_eq_ptStab_of_fixPt_eq hD hE hne hfp, ?_⟩)
    · rw [suborbitSize_cj]; exact suborbitSize_std_r2
    · rw [sup_conj, That_sup_r2, cj_ptStab, fixPt_conj0]
  · have hfp : fixPt (cj g S5Syl) ≠ fixPt (cj g (cj r4 S5Syl)) := by
      rw [fixPt_conj0, fixPt_conj]
      exact fun h => r4_move (g.injective h).symm
    refine Or.inr (Or.inr (Or.inl ⟨hfp, ?_, sup_eq_top_of_fixPt_ne hD hE hfp, ?_⟩))
    · rw [suborbitSize_cj]; exact suborbitSize_std_r4
    · rw [sup_conj, card_cj]; exact card_That_sup_r4
  · have hfp : fixPt (cj g S5Syl) ≠ fixPt (cj g (cj r8 S5Syl)) := by
      rw [fixPt_conj0, fixPt_conj]
      exact fun h => r8_move (g.injective h).symm
    refine Or.inr (Or.inr (Or.inr ⟨hfp, ?_, sup_eq_top_of_fixPt_ne hD hE hfp, ?_⟩))
    · rw [suborbitSize_cj]; exact suborbitSize_std_r8
    · rw [sup_conj, That_sup_r8, cj_top]

end CFSG.Quasithin.F53.Stellmacher.S35.F2a
