module

public import CFSG.Quasithin.Vol2.Ch12Sec7Excl
public import CFSG.Quasithin.Vol2.Ch12Sec2SettingK
public import CFSG.Quasithin.Vol2.Ch12Sec7Ident
public import CFSG.Quasithin.Vol2.KGFact1271He

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint S127

theorem theorem12_7_14_of (hAsc : Asc94_M24He_L52TypeK) (hId : Ident12714)
    (hHe : He1271Excl) : Theorem12_7_14 := by
  intro G _ _ T L V h t ht h18 z hz h45 hGt hVz
  obtain ⟨hz2, hC, hwc⟩ := hId G T L V h t ht h18 z hz h45 hGt hVz
  obtain ⟨hcl, -⟩ := hAsc G z h.hyp.simple h.hyp.qtke.1 hz2 hC hwc
  rcases hcl with hL52 | hM24 | hHe'
  · exact absurd hL52 (not_lieModel_psl_five_two h)
  · exact hM24
  · exact absurd hGt (hHe G T L V h hHe' t ht h18)

end CFSG.Quasithin.H13
