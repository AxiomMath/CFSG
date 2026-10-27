module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBTriAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBTriPair

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover CFSG.Open

theorem rckRowIIAtTri_holds
    (F : Type) [Field F] [Finite F] (σ : F →+* F) (hF : TriField F σ 1) : RCKRowIIAtTri F σ :=
  rckRowIIAtTri_of_modelPair F σ hF (rckTriP_pair F σ hF)

end CFSG.StandardType.RCKK1II
