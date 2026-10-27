module

public import CFSG.Yardstones.M0362f3a873a3.Definitions
public import CFSG.LocalAnalysis.OddStandard.L2Ree.Halves

public section

namespace CFSG.Yardstones.M0362f3a873a3

theorem oddLieThm187bResidualL2Ree_of_halves (h2 : CFSG.OddStandard.L2Ree.L2Half)
    (hR : CFSG.OddStandard.L2Ree.ReeHalf) : OddLieThm187bResidualL2Ree := by
  intro G _ _ L hS hU hlie hQ h5 h6 _ hM S hcyc
  rcases hQ with ⟨p, f, hm⟩ | ⟨f, hm⟩
  · exact h2 G L hS hlie ⟨p, f, hm⟩ h5 h6 hM S hcyc
  · exact hR G L hS hU ⟨f, hm⟩ S hcyc

end CFSG.Yardstones.M0362f3a873a3
