module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.GH74.GLS.SP.Identify

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin.H13.F431.TwoF4


theorem octagonIdentification_of_tits83 (hT : Tits83T8System) : OctagonIdentification := by
  intro X _ _ R K _ _ _ a hR hSimple ha hK hroots
  obtain ⟨φ, hφ⟩ := hT X (Gm K a) R (octSystemOf hR) hroots
  obtain ⟨e⟩ := theorem30_4.{0} X (Gm K a) 8 R (octSystemOf hR) φ hφ
  have htop : (octSystemOf hR).Xplus = ⊤ := xplus_eq_top (octSystemOf hR)
  exact ⟨e.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

end CFSG.Quasithin.Stroth
