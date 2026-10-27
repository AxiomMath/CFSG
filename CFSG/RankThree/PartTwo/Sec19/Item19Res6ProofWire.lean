module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitary
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofD4
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzEight
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem ks1917XGen_of_seitzField_triality
    (hF : SeitzThreeLThreePiField) (hT : SeitzThreeTriality) (hE : TrialityE27Gen) :
    KS1917XGen :=
  ks1917XGen_of_seitzField hF hT ks1917XGenFaithfulUnitary_holds (ks1917XGenFaithfulD4_of hE)

theorem seitz199Outer_of_seitzField_diag
    (hF : SeitzThreeLThreePiField) (hA : Seitz199OuterUnitaryDiag) : Seitz199Outer :=
  seitz199Outer_of_seitzField hF
    (seitz199OuterUnitary_of_seitzThree_diag (SeitzScopeProof.seitzThreeLThreePi_of_field hF) hA)

end CFSG.RankThree.PartTwo.Sec19
