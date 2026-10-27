module

public import Certificates.Data.GMS78RuNModel
public import Certificates.Data.GMS78RuSModelData

public section

namespace CFSG.GMS78RuN

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

@[expose] def gamColCheck : Bool :=
  (List.range 8).all fun j => (List.range 256).all fun c =>
    xs8 c (nBT j) == bC (sBasis.getD j 0) (sMaskN c j)

@[expose] def dPartCheck : Bool :=
  (List.finRange 8).all fun d => (List.range 256).all fun c =>
    sMask (dPart d c).1 == nAd (dCode d) (sMask c) && (dPart d c).2 == nTau (dCode d) (sMask c)

end CFSG.GMS78RuN
