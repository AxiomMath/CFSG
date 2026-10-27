module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.SL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.Sp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.SU4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.OmegaPlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.OmegaMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine

theorem kTab23cNine_holds : KTab23cNine := by
  intro W _ _ H n hN _
  rcases hN with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨a, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ |
    ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact kTab23cNineAt_sl (W := W) H (k := 2) (by norm_num) h
  · exact kTab23cNineAt_sp4 H h
  · exact kTab23cNineAt_sl (W := W) H (k := 3) (by norm_num) h
  · exact kTab23cNineAt_su4 (H := H) h
  · exact kTab23cNineAt_om6m H h
  · exact kTab23cNineAt_sl (W := W) H (k := 4) (by norm_num) h
  · exact kTab23cNineAt_omegaPlusSix H h
  · exact kTab23cNineAt_sp6 H h
  · exact kTab23cNineAt_omegaMinusEight H h

end CFSG.LocalAnalysis.UniquenessCase.UC22
