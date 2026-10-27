module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusGood
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusTag
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Inputs

theorem ggOppositeRadicalUniversalAt_POmegaMinus : GGOppositeRadicalUniversalAt .POmegaMinus := by
  intro n f hadm _
  obtain ⟨-, -, hn⟩ := hadm
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
  refine ⟨GGOppRadOmega.finite_spinGroup_quadMinus (minusCoeffs_irr 2 f), fun z hz _ => ?_,
    fun Q hQne hQ => GGOppRadOmega.ggOppRadGood_minus (minusCoeffs_irr 2 f) hn hQne hQ⟩
  rw [CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn (minusCoeffs_irr 2 f),
    Subgroup.mem_bot] at hz
  exact hz

theorem ggOppositeRadicalCountNormalAt_POmegaMinus :
    GGOppositeRadicalCountNormalAt .POmegaMinus :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_POmegaMinus

end Inputs

section Assembly

theorem ggTwoSignalizerGenInput_of_exceptional
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) : GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_families''' ggOppositeRadicalCountNormalAt_POmegaMinus hF4 hE6 hE7
    hE8 h2E6

end Assembly

end CFSG.StandardType
