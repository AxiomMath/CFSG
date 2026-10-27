module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofCube

public section

namespace CFSG.RankThree.PartTwo.Sec11

section Cube

theorem kFact1117CubeG2_of_ss (hNG : NormCentJ1117G2Ss) (hND : NormCentJ1117D4Ss) :
    KFact1117CubeG2 :=
  kFact1117CubeG2_of_normCent (normCentJ1117G2_of_ss hNG) (normCentJ1117D4_of_ss hND)

end Cube

end CFSG.RankThree.PartTwo.Sec11
