module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Concl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.TorusFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Noncentral
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Weyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.LineChar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Quasithin.H13.U4ParCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par KTabC KTabD

theorem stdConcl {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K) :
    Concl (hypUnitriangular hK 2 0) (lineStab (hypSU hK 2 0) (Pi.single ie1 1))
      (vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1)) := by
  obtain ⟨w, hw, hinv⟩ := exists_weyl hK
  refine ⟨torusE hK, torusE_isElemAbelian hK, card_torusE hK, torusE_le_normalizer hK,
    torusE_inf_vecStab_eq hK, ?_, torusE_noncentral hK, w, hw, hinv⟩
  rw [← torusE_inf_vecStab_eq hK]
  exact card_torusE_inf_vecStab hK

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
