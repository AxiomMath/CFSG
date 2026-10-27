module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLocPt

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.RuF45 CFSG.TitsF46
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem fix_inl_of_mem_titsH {g : ↥titsD} (hg : g.1 ∈ titsH) :
    g • (Sum.inl 0 : Vtx) = Sum.inl 0 := by
  rw [dsmul_inl, RuType.J47.fix_zero_of_mem_titsH hg]

end CFSG.Quasithin.TitsGeo
