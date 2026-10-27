module

public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores

public section

namespace CFSG.RankThree.PartOne.KGD

open CFSG.RankThree.Chevalley

theorem smallRee_family :
    SmallReeNormalizedComponentLocalCoreProductOddImage := by
  intro H _ _ p hp hp3 E hE hEcard t ht ht1 L hL ℓ f hT hEL hSL
  obtain ⟨h1, h2, h3, h4, h5⟩ := small_Ree_normalized_component_local_core_product_odd_image
    hp hp3 hE hEcard ht ht1 hL hT hEL hSL
  exact ⟨componentLocalCoreOddImage_of_residual hL ⟨⟨h1, h2, h3⟩, h4⟩, h5⟩

end CFSG.RankThree.PartOne.KGD
