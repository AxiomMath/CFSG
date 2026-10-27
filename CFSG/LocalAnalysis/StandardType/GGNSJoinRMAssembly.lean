module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBranch
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRealized
public import CFSG.LocalAnalysis.StandardType.GGNSJoinNbrInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

theorem nsReflMaxInputOf_of_inputs {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hTB : GGTBFixInput)
    (hRank : NSRankOneLInputOf T)
    (hBase : NSBaseFrameInputOf T) (hLev2 : GGSecFiveLevTwoInput') (hJA2 : NSJA2InputOf T)
    (hRT : GGWeylReflTripleInput) (hUse : ZS.UseInput) (hWit : ZS.WitnessInput)
    (hOrth : NSOrthExclInputOf T) (hF4R : GGF4ThreeNbrRankInput)
    (hTwE6 : GGTwE6ThreeNbrRankInput) (hTCJ : GGTCJKnown) (hTP : GGSecFiveA8TablePInput)
    (hRaw : GGRawInnFieldInput) (hIso : GGRawInndiagIsoInput) : NSReflMaxInputOf T := by
  have hFix : NSFixInputOf T := nsFixInput_of_tbFix hTB
  have hRootGenL : NSRootGenLInputOf T := nsRootGenLInput_of_rankOne hRank
  have hPumpL : NSPumpLInputOf T := nsPumpLInput_of_baseFrame hBase
  have hPumpNbr : NSPumpNbrInputOf T :=
    nsPumpNbrInput_holds hF4R hL hP hTwE6 hTCJ hTP hRaw hIso
  have hBar : NSBarInputOf T := nsBarInput_holds hL hP hBase hPumpNbr hFix hJA2
  have hJr : NSJrInputOf T := nsJrInput_of_rootGenL hRootGenL
  have hCR : NSCRInputOf T := nsCRInput_of_pump hL hP hPumpL hPumpNbr
  have hCR3 : NSCR3InputOf T := nsCR3Input_of_pump hL hP hPumpL hPumpNbr hRT
  have hWeyl : NSWeylBranchInputOf T :=
    nsWeylBranchInput_of_inputs hBar hJA2 hJr hCR hCR3 hUse hWit hOrth
  exact nsReflMaxInput_of_weylBranch hL hP hFix hRootGenL hBase hLev2 hWeyl

end NSJoin

end CFSG.StandardType

end
