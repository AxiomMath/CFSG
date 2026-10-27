module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanSylowAbelianLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusOmegaMinus8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusSp6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusU6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_CartanSylowAbelian_holds :
    K_CartanSylowAbelian := by
  intro K _ _ t m f r hadm hL hq hZ ht hr hr5 hrd
  rcases ht with ht | ht | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact k_CartanSylowAbelian_linear K t m f r hadm hL hq hZ (Or.inl ht) hr hr5 hrd
  · exact k_CartanSylowAbelian_linear K t m f r hadm hL hq hZ (Or.inr ht) hr hr5 hrd
  · exact k_CartanSylowAbelian_u6 K f r hadm hL hq hZ hr hr5 hrd
  · exact k_CartanSylowAbelian_sp6 K f r hadm hL hq hZ hr hr5 hrd
  · exact k_CartanSylowAbelian_omegaMinus8 K f r hadm hL hq hZ hr hr5 hrd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
