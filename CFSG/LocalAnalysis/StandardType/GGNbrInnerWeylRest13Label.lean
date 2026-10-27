module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylField
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6Split
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLineDecomp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylRest13Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylRest12Label p lab ∧
    (GGNbrWeylFieldRestLabel p lab ∨ GGNbrWeylUnitSixThreeLabel p lab ∨
      GGNbrWeylE6ThreeDvdLabel p lab ∨ GGNbrWeylTwE6RestLabel p lab ∨
      GGNbrWeylExcPlusSmallPrimeLabel p lab)

end CFSG.StandardType
