module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem conclusion76_of_stronglyEmbeddedThree (k : Sec7Core4 G) (hp3 : k.p = 3)
    (hK : StronglyEmbeddedThree) : Conclusion76 k.M k.p :=
  conclusion76_of_steps k (k.step74w_of_stronglyEmbeddedThree hp3 hK)
    (k.step75_of_stronglyEmbeddedThree hp3 hK) (step72L k)
    (k.step76C_of_stronglyEmbeddedThree hp3 hK)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
