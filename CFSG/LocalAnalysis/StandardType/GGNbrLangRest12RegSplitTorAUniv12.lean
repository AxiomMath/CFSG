module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivDefs

public section

namespace CFSG.StandardType

@[expose] def GGNbrLangRest12RegSplitTorAUniv12 : Prop :=
  KGLangTorusNTUnivOn (fun p lab => GGNbrLangRegLabel p lab ∧ GGNbrLangRest12Label p lab) ∧
    KGLangAxisTorAInput ∧ GGNbrLangAxisOn GGNbrLangRest12NonRegNotRankLabel

end CFSG.StandardType
