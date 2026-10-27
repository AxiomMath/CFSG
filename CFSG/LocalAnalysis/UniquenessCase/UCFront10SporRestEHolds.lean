module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRestE
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporLy
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporTh
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONan
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi23Frame
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporHN
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporBThompson
public import CFSG.Monster.B.TwoA.Sp8.TwoRankCbar
public import CFSG.Monster.B.TwoA.Sp8.T8Witness
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMJ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

theorem k105SporRestE_holds :
    K105SporRestE := by
  intro s hs
  cases s
  case ONan => exact k105SporAt_ONan
  case Co1 => exact k105SporAt_Co1
  case Fi23 => exact Fi23K.k105SporAt_fi23
  case Fi24Prime => exact k105SporAt_Fi24Prime
  case HN => exact k105SporAt_HN
  case Ly => exact k105SporAt_Ly
  case Th => exact k105SporAt_Th
  case B => exact BK.k105SporAt_B_of_thompsonJ (BK.hJ_B_of_rank
      CFSG.Monster.B.TwoA.Sp8.WordRel.card_le_of_isElemAbelian_Cbar
      CFSG.Monster.B.TwoA.Sp8.WordRel.exists_four_elemAbelian)
  case M => exact MK.k105SporAt_M_of_certificates
  all_goals exact absurd hs (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
