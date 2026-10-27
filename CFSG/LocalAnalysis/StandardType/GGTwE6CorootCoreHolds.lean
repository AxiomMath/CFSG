module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreOfFuse
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFuse

public section

namespace CFSG.StandardType.TwE6RootAs


theorem twE6CorootCore_holds : TwE6CorootCore :=
  CFSG.StandardType.TwE6CorootCore.twE6CorootCore_of_fuse
    CFSG.StandardType.TwE6CorootCore.exists_conj_eq_thetaSL2_pow

end CFSG.StandardType.TwE6RootAs

end
