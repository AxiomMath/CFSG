module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2Proof
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2Proof
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofRee

public section

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof


theorem kF83ReeCentThree_holds : KF83ReeCentThree :=
  ReeF4Cent2Proof.kF83ReeCentThree_of_orderThreeConj reeF4OrderThreeConj_holds

theorem kF83ReeF4_holds : Item83Proof.KF83ReeF4 :=
  ReeF4Cent2Proof.kF83ReeF4_of_orderThreeConj reeF4OrderThreeConj_holds

theorem census228Ree2F4_holds : Sec21.Census228Ree2F4 :=
  Sec21.census228Ree2F4_of kF83ReeCentThree_holds

end CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
