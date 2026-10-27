module

public import CFSG.LocalAnalysis.StandardType.GGKGAssembly
public import CFSG.LocalAnalysis.StandardType.GGKGGlue
public import CFSG.LocalAnalysis.StandardType.GGKGLin
public import CFSG.LocalAnalysis.StandardType.GGKGUni
public import CFSG.LocalAnalysis.StandardType.GGKGSymp
public import CFSG.LocalAnalysis.StandardType.GGKGOrth
public import CFSG.LocalAnalysis.StandardType.GGKGSmall
public import CFSG.LocalAnalysis.StandardType.GGKGNcE
public import CFSG.LocalAnalysis.StandardType.GGKGNcTwE6
public import CFSG.LocalAnalysis.StandardType.GGKGExcF4

public section

namespace CFSG.StandardType.KG

theorem ggPumpCLabelKnown_holds :
    GGPumpCLabelKnown :=
  ggPumpCLabelKnown_of_kgSimple
    (kgSimple_of_families kgLin_holds kgUni_holds kgSymp_holds kgOrth_holds
      (kgExc_of_split kgExcE_holds kgExcTw_holds kgExcF4_holds kgExcSmall_holds))

end CFSG.StandardType.KG
