module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGAm2ExcBig : Prop :=
  GGTablePKnownR fun p n labJ labX =>
    GGRegimeAm2 p n labJ labX ∧ GGKacExcPair labX p ∧ 2 ≤ labX.n

end CFSG.StandardType

end
