module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusGood
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUPSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Inputs

theorem ggOppositeRadicalUniversalAt_POmegaPlus : GGOppositeRadicalUniversalAt .POmegaPlus := by
  intro n f hadm _
  obtain ⟨-, -, hn4⟩ := hadm
  have hn : 3 ≤ n := by omega
  rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
      plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
  refine ⟨GGOppRadOmega.finite_spinGroup_quadPlus, fun z hz _ => ?_,
    fun Q hQne hQ => GGOppRadOmega.ggOppRadGood_plus hn hQne hQ⟩
  rw [RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn, Subgroup.mem_bot] at hz
  exact hz

theorem ggOppositeRadicalCountNormalAt_POmegaPlus :
    GGOppositeRadicalCountNormalAt .POmegaPlus :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_POmegaPlus

end Inputs

section Assembly

theorem ggTwoSignalizerGenInput_of_families'''
    (hMinus : GGOppositeRadicalCountNormalAt .POmegaMinus)
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) : GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_families'' ggOppositeRadicalCountNormalAt_POmegaPlus hMinus hF4 hE6
    hE7 hE8 h2E6

end Assembly

end CFSG.StandardType
