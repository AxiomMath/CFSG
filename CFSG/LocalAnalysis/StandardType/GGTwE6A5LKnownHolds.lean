module

public import CFSG.LocalAnalysis.StandardType.GGTwE6A5LCells
import CFSG.LocalAnalysis.StandardType.GGTwE6A5LC5TwD5
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusSymplectic
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusOrthPlus
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusOrthMinus

public section

namespace CFSG.StandardType.SCFourCover


theorem ggTwE6A5LKnown_holds : GGTwE6A5LKnown :=
  ggTwE6A5LKnown_of_cells ggTwE6A5LAt_symplectic_five ggTwE6A5LAt_twD_five
    largeEvenLabelAll_torusLift_symplectic_threeFive
    largeEvenLabelAll_torusLift_orthPlus_threeFive
    largeEvenLabelAll_torusLift_orthMinus_threeFive

end CFSG.StandardType.SCFourCover

end
