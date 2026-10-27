module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthExclOfInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4Discharge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchOfInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveOrthExclInput_of_cited
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input) (hRQ : GGReflRealizedQFourNbrInput)
    (hTBJ : GGSecFiveTBJTypeD4Input) (hKSL : GGSecFiveOrthKSLInput)
    (hStruct : GGSecFiveOrthD4KStructInput) : GGSecFiveOrthExclInput :=
  ggSecFiveOrthExclInput_of_inputs hL hP hPump hFix hJA2 hRQ hTBJ hKSL
    (ggSecFiveOrthD4ExclInput_of_inputs hFix hStruct)

theorem ggSecFiveWeylBranchInput_of_cited
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input)
    (hUse : ZS.UseInput) (hWit : ZS.WitnessInput) (hJr : GGSecFiveJrInput) (hCR : GGSecFiveCRInput)
    (hCR3 : GGSecFiveCR3Input) (hRQ : GGReflRealizedQFourNbrInput)
    (hTBJ : GGSecFiveTBJTypeD4Input) (hKSL : GGSecFiveOrthKSLInput)
    (hStruct : GGSecFiveOrthD4KStructInput) : GGSecFiveWeylBranchInput :=
  ggSecFiveWeylBranchInput_of_inputs hL hP hPump hFix hJA2 hUse hWit hJr hCR hCR3
    (ggSecFiveOrthExclInput_of_cited hL hP hPump hFix hJA2 hRQ hTBJ hKSL hStruct)

end CFSG.StandardType

end
