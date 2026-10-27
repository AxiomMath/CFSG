module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Open.Defs

public section

namespace CFSG.KC.L34Cov

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def abLetTabs : Array Tab := #[aST, invTab 42 aST, bST, invTab 42 bST]

end CFSG.KC.L34Cov

end
