module

public import CFSG.LocalAnalysis.StandardType.PhanELocalCodes
import CFSG.LocalAnalysis.StandardType.PhanELocalRank2Chamber
import CFSG.LocalAnalysis.StandardType.PhanELocalRank2Panel
import CFSG.LocalAnalysis.StandardType.PhanELocalRank2Coll
import CFSG.LocalAnalysis.StandardType.PhanELocalRank2Pol
import CFSG.LocalAnalysis.StandardType.PhanELocalRank2Exch

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem phanIrr2 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (c : PhanCode)
    (hc : c.IsIrr2) : ((c.sys K).restrict (c.set K f)).Connected := by
  cases c with
  | a2chamber => exact a2chamber_connected K f hK hq
  | a2panel => exact a2panel_connected K f hK hq
  | a2coll => exact a2coll_connected K f hK hq
  | a2pol => exact a2pol_connected K f hK hq
  | exchA1A1 => exact exchA1A1_connected K f hK hq
  | _ => exact hc.elim

theorem phanModelsRank2 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) : PhanModelsRank2 K f :=
  phanModelsRank2_of_irr K f fun c hc => phanIrr2 K f hK hq c hc

end CFSG.ClassicalInvolution.Phan.PhanE

end
