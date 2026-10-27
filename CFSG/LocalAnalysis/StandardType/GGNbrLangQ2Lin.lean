module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2LinR

public section

namespace CFSG.StandardType


theorem q2RowSolver_linear_holds : Q2RowSolverInput .linear :=
  q2RowSolverInput_of_rLevel q2RLevel_linear

theorem q2RowSolver_fieldTwo_holds : Q2RowSolverInput .fieldTwo :=
  q2RowSolverInput_of_rLevel q2RLevel_fieldTwo

end CFSG.StandardType
