module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofG2
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofMain
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofSp4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofL4

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

open CFSG.RankThree.PartTwo

section Holds

theorem g2ThreeConjSL2_holds : KS11Lie4Proof.G2ThreeConjSL2 :=
  KS11Lie4Proof.g2ThreeConjSL2_of_minus g2ThreeConjSL2Minus_holds

theorem g2ThreeACent_holds : KS11Lie4Proof.G2ThreeACent :=
  KS11Lie4Proof.g2ThreeACent_of_minus g2ThreeACentMinus_holds

end Holds

section KFacts

theorem thetaCentral119G2Ss_holds : ThetaCentral119G2Ss :=
  KS11Lie4Proof.thetaCentral119G2Ss_of_twisted g2ThreeConjSL2Minus_holds g2ThreeACentMinus_holds

theorem centJ119G2Inn_holds : CentJ119G2Inn :=
  KS11Lie4Proof.centJ119G2Inn_of_twisted g2ThreeConjSL2Minus_holds g2ThreeACentMinus_holds

theorem centJ119G2Out_holds : CentJ119G2Out :=
  KS11Lie4Proof.centJ119G2Out_of_twisted g2ThreeConjSL2Minus_holds g2ThreeACentMinus_holds

theorem normCentJ1117G2Ss_holds : NormCentJ1117G2Ss :=
  KS11Lie4Proof.normCentJ1117G2Ss_of_twisted g2ThreeConjSL2Minus_holds g2ThreeACentMinus_holds

theorem census228G2Odd_holds : Sec21.Census228G2Odd :=
  Sec21.census228G2Odd_of_minus g2ThreeConjSL2Minus_holds g2ThreeACentMinus_holds

end KFacts

end CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
