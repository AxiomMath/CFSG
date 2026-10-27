module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinOrthExcl
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRankOneOfRk1
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


namespace NSJoin

theorem nsReflMaxInput_of_orth_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hTBF : GGTBFixInput)
    (hUse : ZS.UseInput) (hWit : ZS.WitnessInput) (hRT : GGWeylReflTripleInput)
    (hLev2 : GGSecFiveLevTwoInput') (hPumpNbr : NSPumpNbrInput) (hRQ : NSRealNbrInputOf NSTypeAD)
    (hBase : NSBaseFrameInput) (hRankOneL : NSRankOneLInput) (hJA2 : NSJA2Input)
    (hNbrQ4 : NSNbrQFourInput) : NSReflMaxInput := by
  have hFix := nsFixInput_of_tbFix (T := NSTypeAD) hTBF
  have hRootGenL := nsRootGenLInput_of_rankOne hRankOneL
  have hPumpL := nsPumpLInput_of_baseFrame hBase
  have hBar := nsBarInput_holds hL hP hBase hPumpNbr hFix hJA2
  have hJr := nsJrInput_of_rootGenL hRootGenL
  have hCR := nsCRInput_of_pump hL hP hPumpL hPumpNbr
  have hCR3 := nsCR3Input_of_pump hL hP hPumpL hPumpNbr hRT
  have hOrth := nsOrthExclInput_holds hL hP hBase hRootGenL hRQ hNbrQ4 hPumpNbr
  have hWeyl := nsWeylBranchInput_of_inputs hBar hJA2 hJr hCR hCR3 hUse hWit hOrth
  exact nsReflMaxInput_of_weylBranch hL hP hFix hRootGenL hBase hLev2 hWeyl

theorem nsJoinPhan_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hTBF : GGTBFixInput)
    (hUse : ZS.UseInput) (hWit : ZS.WitnessInput) (hRT : GGWeylReflTripleInput)
    (hLev2 : GGSecFiveLevTwoInput') (hPumpNbr : NSPumpNbrInput) (hRQ : NSRealNbrInputOf NSTypeAD)
    (hGenP : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput)
    (hBase : NSBaseFrameInput) (hRankOneL : NSRankOneLInput) (hJA2 : NSJA2Input)
    (hNbrQ4 : NSNbrQFourInput) (hLocalGen : NSNbrLocalGenInput) :
    GGSecFiveJoinPhanA5Input ∧ GGSecFiveJoinPhanInput := by
  have hRM := nsReflMaxInput_of_orth_inputs hL hP hTBF hUse hWit hRT hLev2 hPumpNbr hRQ hBase hRankOneL
    hJA2 hNbrQ4
  have hGenN := nsNbrGenKNInput_of_local hGenP hPair hLocalGen
  exact ⟨joinPhanA5_of_reflMax_genN hRM hGenN hGenP hPair,
    joinPhanD_of_reflMax_genN hRM hGenN hGenP hPair⟩


theorem nsJoinPhan_of_types
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hTBF : GGTBFixInput)
    (hUse : ZS.UseInput) (hWit : ZS.WitnessInput) (hRT : GGWeylReflTripleInput)
    (hLev2 : GGSecFiveLevTwoInput') (hPumpNbr : NSPumpNbrInput) (hRQ : NSRealNbrInputOf NSTypeAD)
    (hGenP : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput)
    (hRk1 : GGSecFiveRk1PhanInput)
    (hJA2A : NSJA2InputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hJA2D : NSJA2InputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M))
    (hQ4A : NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hQ4D : NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M))
    (hGenLocA : NSNbrLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hGenLocD : NSNbrLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M)) :
    GGSecFiveJoinPhanA5Input ∧ GGSecFiveJoinPhanInput :=
  nsJoinPhan_of_inputs hL hP hTBF hUse hWit hRT hLev2 hPumpNbr hRQ hGenP hPair
    (nsBaseFrameInputOf_of_lab (T := NSTypeAD) (fun h => h.le_three) hTBF
      (ggTBTorWRows_of_all (ggTBTorAll_of_remaining trivial)) ggTBTorLiftRows_holds)
    (nsRankOneLInput_of_rk1 hRk1)
    (nsJA2Input_of_types hJA2A hJA2D) (nsNbrQFourInput_of_types hQ4A hQ4D)
    (nsNbrLocalGenInput_of_types hGenLocA hGenLocD)

end NSJoin

end CFSG.StandardType

end
