module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.C41PfCorr
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C41Pf

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isC134Case4Corr_local_iff {G₀ R L : Subgroup G} :
    C134CorrLocal.IsC134Case4Corr G₀ R L ↔ MS93.IsC134Case4Corr G₀ R L :=
  Iff.rfl

end C41Pf

end CFSG.Quasithin
