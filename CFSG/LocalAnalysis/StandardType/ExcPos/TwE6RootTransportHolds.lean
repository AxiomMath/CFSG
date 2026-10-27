module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RootTransport
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RootStdPair
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RootModelDecomp

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos


theorem twE6RootTransport_holds : TwE6RootTransport := by
  refine twE6RootTransport_of_pieces ?_ ?_ ?_
  · intro n f
    exact exists_longRoot_twE6 n f
  · intro X _ n f p ψ G₀ B₁ D J x B hB hψr β hβ hβn hlong
    exact twE6_stdPair B hB hψr hβ hβn hlong
  · intro X _ n f p ψ G₀ B₁ D J x B hB hψr a ha
    exact twE6_model_decomp B hB hψr a ha

end CFSG.StandardType.LieKnownR2.ExcPos
