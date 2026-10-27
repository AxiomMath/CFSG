module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUnitaryRoot
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthMinusHolds
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthPlus
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSp
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFHolds
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMRestTwo
public import CFSG.LocalAnalysis.StandardType.GGRemStdSubResidualsU
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneRestFiveExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneMoreExcTwoLabel p lab ∨ GGIOneMoreTwE6Label p lab ∨ GGIOneMoreE6ThreeLabel p lab

section Certs

theorem ggStdSubIOneProperInputOn_restFive_of_exc (ha₀ : GGLNoncyclicInput)
    (hDR : GGIOneUnitaryDvdRootInput) (hDD : GGIOneUnitaryDvdDeltaInput)
    (hF : GGIOneUnitaryFiveTwoInput) (hS : GGIOneSpTwoRootInput)
    (hP : GGIOneOrthPlusFourInput) (hX : GGStdSubIOneProperInputOn GGIOneRestFiveExcLabel) :
    GGStdSubIOneProperInputOn GGIOneProperRestFiveLabel :=
  ((ggStdSubIOneProperInputOn_unitaryRest ha₀ hDR hDD ggIOneUnitaryThreeRootInput_holds hF).or
    ((ggStdSubIOneProperInputOn_twDThreeField_holds ha₀).or
      ((ggStdSubIOneProperInputOn_spTwoRest ha₀ hS).or
        ((ggStdSubIOneProperInputOn_orthPlusFour ha₀ hP).or
          ((ggStdSubIOneProperInputOn_orthMinusOddField_holds ha₀).or hX))))).mono fun _ _ h => h

end Certs

end CFSG.StandardType

