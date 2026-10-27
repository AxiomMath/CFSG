module

public import CFSG.LocalAnalysis.StandardType.GGTBJSudTorus
public import CFSG.LocalAnalysis.StandardType.GGTBRowUdSetup
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.ClassicalGroups.UnitaryFlag

theorem ggTBJTorusNoncomm_rowR5Ud :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN y hy hy1 J' hJ' hJl hcount
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  obtain ⟨d, n, K, _, _, ψ, I, hd, hn, hpd, hpq, hK, hI, hTB, hcard⟩ :=
    ggSudRow_tbGroup hHyp hL hN
  exact ggTBJ_sud_torusJNoncomm hK hn hd hp hpq hpd hI ψ _ hTB hcard y hy hJ' hcount

theorem ggTBJNaWeylQFourOn_rowR5Ud :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm ggTBJTorusNoncomm_rowR5Ud

end CFSG.StandardType

end
