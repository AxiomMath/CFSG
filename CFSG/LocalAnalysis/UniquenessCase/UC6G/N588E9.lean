module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E8
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588F1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

theorem l620_of_inputs (hKM : UCK.KMult) (hK3 : UCK.KMult3) (hSch : UCK.KSch)
    (hK35 : UCK.K35Ω) (hX : UCK.K620Exc) (m : Mz614 Dat)
    (h69 : R6_9 Dat) : m.L620 :=
  m.l620_of_exc hKM hK3 h69 hSch hK35 (m.not_alt_fi22_of_inputs hKM hK3 h69 hSch hX)

end Mz614

theorem l620_field_of_inputs {G : Type} [Group G] [Finite G] {Dat : Data G} (hKM : UCK.KMult) (hK3 : UCK.KMult3) (hSch : UCK.KSch)
    (hK35 : UCK.K35Ω) (hX : UCK.K620Exc) :
    ∀ (m : Mz614 Dat),
      R6_7 Dat → R6_9 Dat → m.L620 :=
  fun m _ h69 => m.l620_of_inputs hKM hK3 hSch hK35 hX h69

end CFSG.LocalAnalysis.UniquenessCase.UC6G
