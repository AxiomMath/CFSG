module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeExceptional
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeOmegaMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeOmegaPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeSymplectic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeTwistedE6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeUnitary
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719


theorem k_CartanRankLarge_holds : K_CartanRankLarge := by
  intro K _ _ t m f hadm hq hL hqs hodd S hS hrank
  cases t with
  | PSL => exact k_CartanRankLarge_psl K m f hadm hq hL hqs hodd S hS hrank
  | PSU => exact k_CartanRankLarge_psu K m f hadm hq hL hqs hodd S hS hrank
  | PSp => exact k_CartanRankLarge_psp K m f hadm hq hL hqs hodd S hS hrank
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus => exact k_CartanRankLarge_pomegaPlus K m f hadm hq hL hqs hodd S hS hrank
  | POmegaMinus => exact k_CartanRankLarge_pomegaMinus K m f hadm hq hL hqs hodd S hS hrank
  | F4 =>
    obtain rfl : m = 0 := hadm.2.2
    exact k_CartanRankLarge_F4 K f hadm hq hL hqs hodd S hS hrank
  | E6 =>
    obtain rfl : m = 0 := hadm.2.2
    exact k_CartanRankLarge_E6 K f hadm hq hL hqs hodd S hS hrank
  | E7 =>
    obtain rfl : m = 0 := hadm.2.2
    exact k_CartanRankLarge_E7 K f hadm hq hL hqs hodd S hS hrank
  | E8 =>
    obtain rfl : m = 0 := hadm.2.2
    exact k_CartanRankLarge_E8 K f hadm hq hL hqs hodd S hS hrank
  | twistedE6 =>
    obtain rfl : m = 0 := hadm.2.2
    exact k_CartanRankLarge_twistedE6 K f hadm hq hL hqs hodd S hS hrank
  | G2 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact absurd hrank (by simp [S17.CS17LieRank])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
