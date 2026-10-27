module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108H207
import CFSG.LocalAnalysis.UniquenessCase.UC22K108Calc
import CFSG.LocalAnalysis.UniquenessCase.UC22K108RowsMain
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigRowX
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BNFam
import CFSG.LocalAnalysis.UniquenessCase.UC22K108D42Row

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10


theorem k108H207_holds : K108H207 :=
  k108H207_of_rows (k108Rows_of_inputs (fun _ h => k108RowX_of_splitBN h) k108FamL2_splitBN
    k108FamSz_splitBN k108FamU3_splitBN k108FamL3_splitBN k108FamSp4_splitBN k108FamG2_splitBN
    k108Fam3D4_splitBN k108Fam2F4_splitBN k108FamU4_splitBN k108FamU5_splitBN k108FamL4_splitBN
    k108FamSp6_splitBN k108FamO8m_splitBN k108Row3D4two_holds)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
