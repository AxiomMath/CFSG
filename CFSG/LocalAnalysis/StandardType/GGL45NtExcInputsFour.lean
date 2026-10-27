module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcCore
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridge
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrame
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameRee
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralHolds
public import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
public import CFSG.LocalAnalysis.StandardType.GGL45NtFinal
public import CFSG.LocalAnalysis.StandardType.GGL45NtClLabels
public import CFSG.HardMathSupport.C14F4Lattice

public section

namespace CFSG.StandardType

open CFSG.HardMathSupport.C14Idx

theorem ggL45NtCoreOn_ex_of_four_inputs
    (hIdx : ExcIdxFrobInput) (hBor : ExcBorelInput) (hIdxRee : ExcIdxReeInput)
    (hStab : ExcReeCentralStab) :
    GGL45NtCoreOn GGL45NtFamEx :=
  open CFSG.HardMathSupport.C14Exc CFSG.StandardType.LieCore in
  ggL45NtCoreOn_ex_of_bridge (fun L _ _ _ => excBridge_U L) (fun L _ _ _ => excBridge_E6 L)
    (fun L _ _ _ => excBridge_twE6 L) (fun L _ _ _ => excBridge_triD4 L)
    (fun L _ _ _ _ _ => excBridge_twF4 L)
    (excAlgGeoStd_of_frame ggLieToralPosition_holds ggLieLangPosition_holds hIdx hBor)
    (excAlgGeoRee_of_frame ggLieToralPosition_holds ggLieLangPosition_holds hBor hIdxRee
      CFSG.HardMathSupport.C14F4Lattice.excF4PowSixInput hStab)

theorem ggL45TorusHKnownFormsOn_nonTorsion_of_four_inputs
    (hIdx : ExcIdxFrobInput) (hBor : ExcBorelInput) (hIdxRee : ExcIdxReeInput)
    (hStab : ExcReeCentralStab) :
    GGL45TorusHKnownFormsOn GGL45FamNonTorsion :=
  ggL45Nt_torusHKnownFormsOn_nonTorsion_of_core ggL45NtCoreOn_cl
    (ggL45NtCoreOn_ex_of_four_inputs hIdx hBor hIdxRee hStab)

end CFSG.StandardType
