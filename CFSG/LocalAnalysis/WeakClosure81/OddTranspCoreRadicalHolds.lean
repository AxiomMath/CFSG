module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreCases
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalList
public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.LocalAnalysis.WeakClosure81


theorem oddTranspCoreRadicalInput_holds : OddTranspCoreRadicalInput := by
  intro X _ _ s hord hodd hncl _ _ hR h3
  exact CoreRadical.configBC_of_solvableRadical_le_center hord hodd hncl hR h3

end CFSG.LocalAnalysis.WeakClosure81
