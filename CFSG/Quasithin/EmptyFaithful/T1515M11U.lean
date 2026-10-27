module

public import CFSG.Quasithin.EmptyFaithful.T1515M11
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine

theorem psuThreeThreeOrder1522 : PSUThreeThreeOrder := by
  intro X _ h
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (↥(StatedSU 3 3 F) ⧸ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 3 F)) = _
  rw [← Subgroup.index, statedScalars_subgroupOf_statedSU_eq_bot hF9, Subgroup.index_bot]
  exact card_statedSU hF9

end CFSG.Quasithin
