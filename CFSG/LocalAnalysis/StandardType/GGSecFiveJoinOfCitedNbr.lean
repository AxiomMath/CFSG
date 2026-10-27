module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxOfInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNbrGenKNOfLeaves
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJNormOfFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreHolds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylReflTriple
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOfUniOrth
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaUniFinal
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOrthFinal
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpLOfFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootGenLOfFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveJoinRegionInput_of_cited_nbr
    (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpNbrInput) (hFix : GGSecFiveFixInput)
    (hJA2 : GGSecFiveJA2Input) (hUse : ZS.UseInput) (hWit : ZS.WitnessInput)
    (hRQ : GGReflRealizedQFourNbrInput)
    (hTBJ : GGSecFiveTBJTypeD4Input) (hKSL : GGSecFiveOrthKSLInput)
    (hStruct : GGSecFiveOrthD4KStructInput)
    (hLev2 : GGSecFiveLevTwoInput') :
    GGSecFiveJoinRegionInput := by
  have hSch := CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hL : GGLBalanceInput := ggLBalanceInput_of_catalogueSchreier hSch
  exact ggSecFiveJoinRegionInput_of_primed
    (ggSecFiveReflMaxInput'_of_inputs hL hP ⟨ggSecFivePumpLInput_holds, hPump⟩ hFix hJA2 hUse hWit
      ggWeylReflTripleInput_holds hRQ hTBJ hKSL hStruct ggSecFiveRootGenLInput_holds hLev2)
    (s2jn_ggSecFiveNbrGenKNInput'_of_leaves hSch
      (TCJ.ggTCJEnnolaKnown_of_uni_orth TCJ.innDiagAllEnnolaUni TCJ.innDiagAllEnnolaOrth) hP
      ggJRootCoreInput_holds)
    ggSecFiveJNormInput'_holds

end CFSG.StandardType

end
