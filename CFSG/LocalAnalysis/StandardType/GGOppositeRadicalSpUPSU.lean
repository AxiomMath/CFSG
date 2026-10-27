module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUWitt
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUPSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

section Inputs

theorem ggOppositeRadicalUniversalAt_PSU : GGOppositeRadicalUniversalAt .PSU := by
  intro n f hadm _
  obtain ⟨-, hf, hn, hnq⟩ := hadm
  have hF := card_galoisField_two_mul 2 f hf
  have hU : ggU .PSU n f = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
      Unitary.rootDatum hF n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [hU]
  exact ⟨inferInstance, fun z hz h2 => GGOppRadSpU.eq_one_of_mem_center_su hF hn hnq hz h2,
    fun Q hQne hQ => GGOppRadSpU.ggOppRadGood_su hF hn hnq
      (GGOppRadSpU.ggSUIsoFlagStdAt_of_wittChain hF (GGOppRadSpU.ggSUWittChainAt hF n)) hQne hQ⟩

theorem ggOppositeRadicalCountNormalAt_PSU : GGOppositeRadicalCountNormalAt .PSU :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_PSU

theorem ggOppositeRadicalCountNormalInput_of_families''
    (hPlus : GGOppositeRadicalCountNormalAt .POmegaPlus)
    (hMinus : GGOppositeRadicalCountNormalAt .POmegaMinus)
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) :
    GGOppositeRadicalCountNormalInput :=
  ggOppositeRadicalCountNormalInput_of_families' ggOppositeRadicalCountNormalAt_PSU hPlus hMinus
    hF4 hE6 hE7 hE8 h2E6

end Inputs

section Assembly

theorem ggTwoSignalizerGenInput_of_families''
    (hPlus : GGOppositeRadicalCountNormalAt .POmegaPlus)
    (hMinus : GGOppositeRadicalCountNormalAt .POmegaMinus)
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) : GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_families' ggOppositeRadicalCountNormalAt_PSU hPlus hMinus hF4 hE6 hE7
    hE8 h2E6

end Assembly

end CFSG.StandardType
