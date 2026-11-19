module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoDAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLnLoc

@[expose] public section

namespace Certificates

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.TitsGeo

def titsGeoFacts : Prop :=
  PtLoc ↥titsD octGraph (Sum.inl 0) (ofCode 87) (Sum.inr 0) ∧
    (∃ lab : ZMod 5 → Vtx, AffLab ↥titsD octGraph (Sum.inl 0) lab) ∧
    LnLoc ↥titsD octGraph (Sum.inr 0) (ofCode 45) (ofCode 1862) (ofCode 1896) ∧
    IsGenPolygon octGraph 8

end Certificates

