module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplR.RadicalFixed
public import CFSG.Quasithin.AppendixH.H9.H93.ExplR.RadicalGamma

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

theorem Rg4_le_Lg : Rg4 ≤ Lg 4 := by
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact pairActN_mem_Lg _

theorem Rg4_isElemAbelian2 : IsElemAbelian2 Rg4 := by
  rw [← radicalHom_range]
  exact radicalHom_range_isElemAbelian2

theorem Rg4_card : Nat.card Rg4 = 16 := by
  rw [← radicalHom_range]
  exact card_radicalHom_range

theorem rank_Rg4 : rk ↥(fixV Rg4) = 4 ∧ E3.gammaCheck 2 Rg4 = ⊤ := by
  exact ⟨rk_fixV_Rg4, gammaCheck_two_Rg4⟩

end CFSG.ASVolI.ChH
