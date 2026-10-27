module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ACandidateU34
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34AutE8Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_U34ACand_holds : K_U34ACand :=
  k_U34ACand_of_autE8 k_U34AutE8_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
