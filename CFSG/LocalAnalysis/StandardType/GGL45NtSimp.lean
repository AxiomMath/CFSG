module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtSimpOn_all
    (S : ℕ → LargeEvenLabel → Prop) : GGL45NtSimpOn S :=
  fun _ _ _ _ hlab _ _ =>
    (TCJ.ggTCJ_datum_marking hlab).mono fun _ _ _ _ h hna => (h.2 hna).1

end CFSG.StandardType
