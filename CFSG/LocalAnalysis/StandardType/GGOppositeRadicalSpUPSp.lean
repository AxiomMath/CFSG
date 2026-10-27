module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalPSL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem ggOppositeRadicalUniversalAt_PSp : GGOppositeRadicalUniversalAt .PSp := by
  intro n f _ _
  have hf : Finite (StatedSp n (GaloisField 2 f)) := inferInstance
  exact ⟨hf, fun z hz h2 => GGOppRadSpU.eq_one_of_mem_center_sp (K := GaloisField 2 f) hz h2,
    fun Q hQne hQ => GGOppRadSpU.ggOppRadGood_sp (K := GaloisField 2 f) hQne hQ⟩

theorem ggOppositeRadicalCountNormalAt_PSp : GGOppositeRadicalCountNormalAt .PSp :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_PSp

theorem ggOppositeRadicalCountNormalInput_of_families'
    (hPSU : GGOppositeRadicalCountNormalAt .PSU)
    (hPlus : GGOppositeRadicalCountNormalAt .POmegaPlus)
    (hMinus : GGOppositeRadicalCountNormalAt .POmegaMinus)
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) :
    GGOppositeRadicalCountNormalInput :=
  ggOppositeRadicalCountNormalInput_of_families hPSU ggOppositeRadicalCountNormalAt_PSp hPlus
    hMinus hF4 hE6 hE7 hE8 h2E6

end Inputs

section Assembly

theorem ggTwoSignalizerGenInput_of_families'
    (hPSU : GGOppositeRadicalCountNormalAt .PSU)
    (hPlus : GGOppositeRadicalCountNormalAt .POmegaPlus)
    (hMinus : GGOppositeRadicalCountNormalAt .POmegaMinus)
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) : GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_families hPSU ggOppositeRadicalCountNormalAt_PSp hPlus hMinus hF4
    hE6 hE7 hE8 h2E6

end Assembly

end CFSG.StandardType
