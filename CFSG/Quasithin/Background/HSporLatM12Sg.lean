module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs

public section

namespace CFSG.Quasithin.H.MathieuLat

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m12a m12b)

@[expose] noncomputable def m12Sg : List ↥CFSG.Blueprint.NativeSporadic.M12 :=
  m12Qp.map fun p => (slpElts m12a m12b m12Prog).getD p.1 1

end CFSG.Quasithin.H.MathieuLat

end
