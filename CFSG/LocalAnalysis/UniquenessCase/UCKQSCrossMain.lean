module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSReduction
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSAlt
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSSpor
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSDef
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossL
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossO
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossExcE
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossExcS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

section Cross

theorem pcaLieCross_holds : ∀ t, PCALieCrossAt t := fun t => by
  cases t
  · exact pcaLieCross_PSL
  · exact pcaLieCross_PSU
  · exact pcaLieCross_PSp
  · exact pcaLieCross_POmegaOdd
  · exact pcaLieCross_POmegaPlus
  · exact pcaLieCross_POmegaMinus
  · exact pcaLieCross_G2
  · exact pcaLieCross_F4
  · exact pcaLieCross_E6
  · exact pcaLieCross_E7
  · exact pcaLieCross_E8
  · exact pcaLieCross_twistedE6
  · exact pcaLieCross_trialityD4
  · exact pcaLieCross_twistedB2
  · exact pcaLieCross_twistedG2
  · exact pcaLieCross_twistedF4
  · exact pcaLieCross_Tits

end Cross

section Main

theorem kqs_holds : UCK.KQS :=
  kqs_of_pca
      (pca_of_cases pcaAlt_holds (pcaLie_of_tags pcaLieDef_holds pcaLieCross_holds) pcaSpor_holds)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK
