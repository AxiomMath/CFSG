module

public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine
import CFSG.OddTranspositions.TheoremTwo.ThirdKBenderHolds
import CFSG.OddTranspositions.TheoremTwo.ConfigStatement
import CFSG.OddTranspositions.TheoremTwo.PropFourSeven
import CFSG.OddTranspositions.TheoremTwo.DiffBlock

public section

namespace CFSG.OddTranspositions

theorem fibreSingletonStatement_holds : FibreSingletonStatement :=
  fun _ _ _ _ hC _ _ _ _ _ _ _ hQ => QZ.Config.fibre_singleton hC hQ

theorem thirdKindExclusionStep_of_open
    (h41 : DiffBlockStatement) (h42 : QCentralStatement) (h49 : TheoremFourNineStatement) :
    ThirdKindExclusionStep :=
  thirdKindExclusionStep_of_pieces thirdKBenderStatement_holds h41 h42 configStatement_holds
    fibreSingletonStatement_holds h49

theorem thirdKindExclusionStep_of_diffBlock_qCentral
    (h41 : DiffBlockStatement) (h42 : QCentralStatement) : ThirdKindExclusionStep :=
  thirdKindExclusionStep_of_open h41 h42 QZ.theoremFourNineStatement_holds

theorem aschbacherTheoremTwo_of_diffBlock_qCentral
    (h41 : DiffBlockStatement) (h42 : QCentralStatement) (hlite : TheoremTwoLiteStep) :
    AschbacherTheoremTwo :=
  aschbacherTheoremTwo_of_steps (thirdKindExclusionStep_of_diffBlock_qCentral h41 h42) hlite

theorem aschbacherTheoremTwo_of_qCentral
    (h42 : QCentralStatement) (hlite : TheoremTwoLiteStep) : AschbacherTheoremTwo :=
  aschbacherTheoremTwo_of_diffBlock_qCentral diffBlockStatement_holds h42 hlite

end CFSG.OddTranspositions

end
