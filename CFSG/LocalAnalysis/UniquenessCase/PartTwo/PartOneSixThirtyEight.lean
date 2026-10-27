module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.LocalAnalysis.UniquenessCase.UC22P22za
import CFSG.LocalAnalysis.UniquenessCase.UC611f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r6_38_dataOfSetup (hS : Standing G) (S : Setup G) : UC6.R6_38 (dataOfSetup hS S) :=
  UC6.r6_38_of_sigma23 _ (UC6S846.sigmaStd_dataOfSetup hS S).sig1_sp
    (uc22p22q_r6_38_23_of_print _ (sigma23Std_ofSetup hS S) (r6_1_dataOfSetup hS S)
      (UC6.r6_11Used_dataOfSetup hS S) (sigma2Print_ofSetup hS S)
      (uc22p22q_r613ident_of _ (sigma23Std_ofSetup hS S) (r6_1_dataOfSetup hS S)
        (sigma2Print_ofSetup hS S))
      (r613cent_ofSetup hS S))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
