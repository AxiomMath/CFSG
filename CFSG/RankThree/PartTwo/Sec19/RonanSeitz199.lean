module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofDefs
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSeitz
import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoFinal
import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactCore
import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzEight
import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.Item19ResProofSeitz199

public section

namespace CFSG.RankThree.PartTwo.Sec19.RonanSeitz199

open CFSG.RankThree.PartTwo.Sec19

theorem seitzThreeLThreePi_holds :
    SeitzThreeLThreePi :=
  SeitzScopeProof.seitzThreeLThreePi_of_field seitzThreeLThreePiField_holds

theorem seitz199OuterUnitary_holds :
    Seitz199OuterUnitary :=
  seitz199OuterUnitary_of_seitzThree_diag seitzThreeLThreePi_holds seitz199OuterUnitaryDiag_holds

theorem seitz199Outer_holds :
    Seitz199Outer :=
  seitz199Outer_of_seitzThree seitzThreeLThreePi_holds seitz199OuterUnitary_holds

end CFSG.RankThree.PartTwo.Sec19.RonanSeitz199
