module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2OffRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2SpR

public section

namespace CFSG.StandardType


theorem q2RowSolver_symplectic_holds : Q2RowSolverInput .symplectic :=
  q2RowSolverInput_of_rLevel q2RLevel_symplectic

theorem ggBstarAbelianPreimageJLinResOffRowsInput_of_offSymp
    (h : GGBstarAbelianPreimageJLinResOffRowsInput fun kind =>
      kind = .orthogonalPlus ∨ kind = .linear ∨ kind = .fieldTwo ∨
        kind = .e6Three ∨ kind = .e7Seven ∨ kind = .e8Three ∨ kind = .orthogonalMinus ∨
        kind = .symplectic) :
    GGBstarAbelianPreimageJLinResOffRowsInput fun kind =>
      kind = .orthogonalPlus ∨ kind = .linear ∨ kind = .fieldTwo ∨
        kind = .e6Three ∨ kind = .e7Seven ∨ kind = .e8Three ∨ kind = .orthogonalMinus := by
  refine ggBstarAbelianPreimageJLinResOffRowsInput_of_rows (fun kind hT hS => ?_) h
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hS (by simp)).elim
  · exact (hS (by simp)).elim
  · exact (hS (by simp)).elim
  · exact (hS (by simp)).elim
  · exact (hS (by simp)).elim
  · exact (hS (by simp)).elim
  · exact (hS (by simp)).elim
  · exact q2RowSolver_symplectic_holds

theorem ggBstarAbelianPreimageJLinResOffRowsInput_of_census (hc : Q2ResidualCensusInput) :
    GGBstarAbelianPreimageJLinResOffRowsInput fun kind =>
      kind = .orthogonalPlus ∨ kind = .linear ∨ kind = .fieldTwo ∨
        kind = .e6Three ∨ kind = .e7Seven ∨ kind = .e8Three ∨ kind = .orthogonalMinus ∨
        kind = .symplectic := by
  intro G instG instFin p B Bs x L D J hcfg hInner hN d K instK instFinK θ hpd hpq hoff
  obtain ⟨kind, hmark⟩ := hc G p B Bs x L D J hcfg hInner hN d K θ hpd hpq
  refine (hoff kind ?_ hmark).elim
  cases kind <;> simp

end CFSG.StandardType
