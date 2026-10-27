module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBEnd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem ngAbstract_holds : NGAbstract := by
  intro G _ _ V T N L₁ L₂ hH9 hTN hNM hL₁ hL₂ hstar h763 X _ _ π hπ hker hF
  have c : NGW.Ctx15 V T N L₁ L₂ π := ⟨hH9, hTN, hNM, hL₁, hL₂, hstar, hπ, hker, hF⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨U, u, w⟩ := c.exists_witness hcon.1
  exact c.false_of_witness h763 w hcon.2

end CFSG.LocalAnalysis.WeakClosure81
