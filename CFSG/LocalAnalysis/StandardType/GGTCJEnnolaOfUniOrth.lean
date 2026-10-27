module

public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaGlue
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaFam
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaExc
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangInner
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentPerm

public section

namespace CFSG.StandardType.TCJ

open CFSG.LocalAnalysis.GLTheoremA.Y10GField

theorem ggTCJEnnolaKnown_of_uni_orth
    (hU : InnDiagAllEnnolaOn FamUni) (hO : InnDiagAllEnnolaOn FamOrth) : GGTCJEnnolaKnown :=
  ggTCJEnnolaKnown_of_simple (tcjEnnolaSimple_of_families hU hO
    (innDiagAllEnnolaExc CFSG.LocalAnalysis.GLTheoremA.KD264Lie.lieCompIdxEnnola_exc))

end CFSG.StandardType.TCJ

end
