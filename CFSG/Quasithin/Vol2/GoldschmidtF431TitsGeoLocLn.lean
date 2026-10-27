module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLocPtMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLnLoc

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.RuF45 CFSG.TitsF46
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem fix_inr_of_mem_titsN {g : ↥titsD} (hg : g.1 ∈ titsN) :
    g • (Sum.inr 0 : Vtx) = Sum.inr 0 := by
  rw [dsmul_inr, Sum.inr.injEq, lineHom_eq_iff]
  exact RuType.J47.line_fix_of_mem_titsN hg

end CFSG.Quasithin.TitsGeo
