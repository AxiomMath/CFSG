module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNEnd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem nfAbstract_holds : NFAbstract := by
  intro G _ _ V T N L hH9 hTN hNM _ _ hstar X _ _ π hπ hker hF
  have c : NFW.Ctx V T N π ((L.subgroupOf N).map π) := ⟨hH9, hTN, hNM, hstar, hπ, hker, hF⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨U, u, w⟩ := c.exists_witness hcon.1
  exact c.false_of_witness w hcon.2

end CFSG.LocalAnalysis.WeakClosure81
