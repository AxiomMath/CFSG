module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof


theorem thetaCentral119D4Ss_holds : ThetaCentral119D4Ss :=
  KS11Lie4Proof.thetaCentral119D4Ss_of d4ThreeConj_holds d4ThreeACent_holds d4ThreeBCent_holds

theorem centJ119D4Inn_holds : CentJ119D4Inn :=
  KS11Lie4Proof.centJ119D4Inn_of d4ThreeConj_holds d4ThreeACent_holds d4ThreeBCent_holds

theorem centJ119D4Out_holds : CentJ119D4Out :=
  KS11Lie4Proof.centJ119D4Out_of d4ThreeConj_holds d4ThreeACent_holds d4ThreeBCent_holds
    KS11Lie5Proof.d4ShortOut_holds

theorem normCentJ1117D4Ss_holds : NormCentJ1117D4Ss :=
  KS11Lie4Proof.normCentJ1117D4Ss_of d4ThreeConj_holds d4ThreeACent_holds d4ThreeBCent_holds
    d4NormCent_holds

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
