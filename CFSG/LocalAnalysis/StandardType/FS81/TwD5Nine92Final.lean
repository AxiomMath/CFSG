module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Assembly
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92PumpupTrivial
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Final
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamPSL
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamPSp
public import CFSG.HardMathSupport.Dickson.Sec6.Residuals
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutOrth
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutTwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalFus
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalHeis
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalHeisMat
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATMain
public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197Alg
public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.L3S197Lift
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop51Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporFive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporLarge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporTh7
public import Certificates.Certificate17632Base

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.HardMathSupport.Dickson.Sec6


theorem t5Nine92Norm_of_omega (hΩ : UpD42ExclInnAt IsOmegaTwoBigIndex) : T5Nine92Norm := by
  refine t5Nine92Norm_of_pumpupTrivial CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds ?_
  intro _ _ _ _ _ _ hstd hKproper _ _ hB hrec hfus _ _ hL hbN hJ
  exact mem_dQ_of_census upD42Statement_of_certificates hΩ hstd hKproper hB hrec hfus hL hbN hJ

end CFSG.StandardType.FrameRoute.FS81

end
