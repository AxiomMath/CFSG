module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
import CFSG.LocalAnalysis.StandardType.GGQ2FrameEleH

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

theorem linEleH_holds : LinEleH := by
  intro G _ _ H E t ε K _ _ _ hEN ζ fr hHp hEab hC3
  refine le_of_cover_intertwine hEN fr.π fr.surj fr.ker_le fr.rho ?_ hHp hEab hC3
  intro b h
  have hinter := fr.intertwine (fr.τ.symm b) h
  rw [fr.τ.apply_symm_apply b] at hinter
  exact hinter

end CFSG.StandardType.GGQ2Frame.LinPlacement
