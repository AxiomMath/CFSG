module

public import CFSG.Quasithin.Background.C1CampbellConnect
public import CFSG.Quasithin.Background.C1GNSolv
public import CFSG.Quasithin.EmptyFaithful.S14111Alt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem gNCampbellC128Solv_of (h118 : TheoremC118) (h126 : TheoremC126) (h127 : TheoremC127)
    (h19 : TheoremC19) (h116 : TheoremC116Two) : GNCampbellC128Solv := by
  intro G _ _ T hsimple hqtke hsyl hT0
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) h118
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair T hsyl.1 hT0
  refine ⟨C₁ T, C₂ T, h1ne, h1Z, h1char, h2ne, h2B, h2char, fun M hM hsolv => ?_⟩
  obtain ⟨hMchar, hMsq, hSylM⟩ := inM_facts hsimple hqtke hsyl hM
  exact C1GN.lemma_C128_solv hC (h126 G C₁ C₂ hC) (h127 G) (h19 G) (h116 G)
    hMchar hMsq hSylM hT0 hsolv

end CFSG.Quasithin
