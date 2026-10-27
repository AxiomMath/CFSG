module

public import CFSG.OddTranspositions.TheoremTwo.SevenOneAssembly
import CFSG.OddTranspositions.SevenFourEight.Assembly
import CFSG.OddTranspositions.TheoremTwo.QCentral

public section

namespace CFSG.OddTranspositions

theorem theoremTwoLiteStep_holds :
    TheoremTwoLiteStep := by
  intro G _ _ D hC hrad hsecond hmin
  by_contra hnot3
  exact false_of_sevenSetting hC hrad hsecond hnot3 hmin

theorem aschbacherTheoremTwo_of_qCentralStatement
    (h42 : QCentralStatement) : AschbacherTheoremTwo :=
  aschbacherTheoremTwo_of_qCentral h42 theoremTwoLiteStep_holds

theorem aschbacherTheoremTwo_holds :
    AschbacherTheoremTwo :=
  aschbacherTheoremTwo_of_qCentralStatement qCentralStatement_holds

end CFSG.OddTranspositions

end
