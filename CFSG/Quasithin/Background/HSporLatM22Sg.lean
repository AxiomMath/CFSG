module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs

public section

namespace CFSG.Quasithin.H.MathieuLat

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m22a m22b)

@[expose] noncomputable def m22Sg : List ↥CFSG.Blueprint.NativeSporadic.M22 :=
  m22Qp.map fun p => (slpElts m22a m22b m22Prog).getD p.1 1

end CFSG.Quasithin.H.MathieuLat

end
