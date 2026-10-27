module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpCaseDefs
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2261
public import Certificates.Certificate2269
public import Certificates.Certificate8032
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSA
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabel
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveBPermOffSpInput_of_cases
    (hLin : GGSecFiveBPermOffSpLinInput) (hUni : GGSecFiveBPermOffSpUniInput)
    (hPro : GGSecFiveBPermOffSpProperInput) : GGSecFiveBPermOffSpInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hR
  rcases (GGInnerDiagOnLabel.elim_or (S := fun p lab => GGSecFiveBPermLinLabel n p lab)
      (T := fun p lab => GGSecFiveBPermUniLabel n p lab)
      (ggSecFiveBPermLabelInput_holds G p B Bs x L D J 𝒦 hR n hn eta hAut)) with hL | hU
  · have hB : B = Bs := by
      refine (ggSecFiveRoute_bstar_eq_of_split hR (ggSplitLie_of_rowSA hp ?_)).symm
      refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ?_) hL
      obtain ⟨⟨htag, hrank, hdvd⟩, -⟩ := h
      exact ⟨Or.inl ⟨htag, by omega⟩, hdvd⟩
    exact hLin G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hL
  · by_cases hB : B = Bs
    · exact hUni G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
    · exact hPro G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU

end CFSG.StandardType

end
