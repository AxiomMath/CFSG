module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E8
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588F1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

namespace Mz614

variable {G : Type} [Group G] [Finite G]

theorem l620_of_inputs (hKM : UCK.KMult) (hK3 : UCK.KMult3) (hSch : UCK.KSch)
    (hK35 : UCK.K35Ω) (hX : UCK.K620Exc) (m : Mz614 G)
    (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) : m.L620 :=
  m.l620_of_exc hKM hK3 h69 hSch hK35 (m.not_alt_fi22_of_inputs hKM hK3 h69 hSch hX)

end Mz614

theorem l620_field_of_inputs (hKM : UCK.KMult) (hK3 : UCK.KMult3) (hSch : UCK.KSch)
    (hK35 : UCK.K35Ω) (hX : UCK.K620Exc) :
    ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.L620 :=
  fun _ _ _ m _ h69 => m.l620_of_inputs hKM hK3 hSch hK35 hX h69

end CFSG.LocalAnalysis.UniquenessCase.UC6
