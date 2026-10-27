module

public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOrthLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.TCJ

open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamOrth)

theorem innDiagAllEnnolaOrth :
    InnDiagAllEnnolaOn FamOrth :=
  tcjOrth_innDiagAllEnnolaOrth_of_ggLabelRigidInput
    CFSG.StandardType.ggLabelRigidInput_holds

end CFSG.StandardType.TCJ

end
