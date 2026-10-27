module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.RankThree.GF2n.Tim79aCitedInvol
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma37Defs
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma38
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

theorem card_sl23_p6 : Nat.card CFSG.OddStandard.Solomon75.SL23 = 24 := by
  rw [CFSG.GorensteinWalter.sl2_card_formula (ZMod 3)]
  norm_num [Nat.card_zmod]

theorem card_center_sl23_p6 :
    Nat.card (Subgroup.center CFSG.OddStandard.Solomon75.SL23) = 2 := by
  exact CFSG.ABGLocalTools.card_center_sl2 (F := ZMod 3) (by norm_num [Nat.card_zmod])

end CFSG.RankThree.GF2n.Parrott
