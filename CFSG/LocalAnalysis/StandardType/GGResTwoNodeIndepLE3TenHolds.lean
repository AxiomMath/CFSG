module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenGroup

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwoNodeIndepLE3TenInput_holds
    (hKG : GGReflClassLargeInput') (hLNC : GGLNoncyclicInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput) :
    GGResTwoNodeIndepLE3TenInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  obtain ⟨hrow, hyK, -, hcard, hLY, hLn⟩ := hP
  exact ggTwoNodeTen_weyl hKG hLNC hFix hFixK hD hJ2 hH hrow hyK hcard hLY hLn

end CFSG.StandardType

end
