module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank2
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A1111
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A211
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A22p
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A22x
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13c
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13p
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4c
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4p
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3Exch

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem phanIrr3 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (c : PhanCode)
    (hc : c.IsIrr3) : ((c.sys K).restrict (c.set K f)).Connected ∧
      ((c.sys K).restrict (c.set K f)).SimplyTwoConnected := by
  cases c with
  | a3_1111 => exact a3_1111_models K f hK hq
  | a3_211 => exact a3_211_models K f hK hq
  | a3_121 => exact a3_121_models K f hK hq
  | a3_22p => exact a3_22p_models K f hK hq
  | a3_22x => exact a3_22x_models K f hK hq
  | a3_13c => exact a3_13c_models K f hK hq
  | a3_13p => exact a3_13p_models K f hK hq
  | a3_4c => exact a3_4c_models K f hK hq
  | a3_4p => exact a3_4p_models K f hK hq
  | exchA2A1 => exact exchA2A1_models K f hK hq
  | _ => exact hc.elim

theorem phanModelsRank3 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) : PhanModelsRank3 K f :=
  phanModelsRank3_of_irr K f (phanModelsRank2 K f hK hq) fun c hc => phanIrr3 K f hK hq c hc

end CFSG.ClassicalInvolution.Phan.PhanE

end
