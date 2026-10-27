module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrth
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmall
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSel
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthTransfer
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthFixOmega
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthFormsOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggResExactTwoOrthQTwoOn_holds
    (hRig : GGLabelRigidInput) (hKG : GGReflClassLargeInput') :
    GGResExactTwoOrthQTwoOn (4 ≤ ·) :=
  ggResExactTwoOrthQTwoOn_of_small hRig hKG
    (ggResExactTwoOrthQTwoOn_four_five hRig
      (ggResExactTwoOrthFixLeaf_of_omega ggResExactTwoOrthFixOmega_holds)
      (ggResExactTwoOrthDFourLeaf_of_omega ggResExactTwoOrthFormsOmega_holds)
      (ggResExactTwoOrthTwDFiveLeaf_of_omega ggResExactTwoOrthFormsOmega_holds)
      ggResExactTwoOrthSelLeaf_holds)

end CFSG.StandardType
