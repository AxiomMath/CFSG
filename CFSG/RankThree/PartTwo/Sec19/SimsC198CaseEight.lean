module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Cases
import CFSG.RankThree.PartTwo.Sec19.SimsC198Close
import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso
import CFSG.RankThree.PartTwo.Sec19.SimsC198Rank2

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

theorem caseHolds_eight :
  CaseHolds Alt42Eight := by
  intro X _ _ hX c L 𝒟 hD h
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.quasisimple.2.1
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ |
    ⟨b, d, hbd, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact absurd hD ((noLocalDatum_of_L52 e).noAutDatum c L 𝒟)
  · exact (false_of_rankHyp_PSU5_two hX (by norm_num) e).elim
  · exact absurd hD (noAutDatum_of_L62 e c L 𝒟)
  · exact (false_of_rankHyp_PSU6_two hX e).elim
  · exact absurd hD (noAutDatum_of_L72 e c L 𝒟)
  · exact absurd hD (noAutDatum_of_Sp62 e c L 𝒟)
  · exact (false_of_rankHyp_Sp8_two hX e).elim
  · exact (false_of_rankHyp_OmegaPlus_two hX e).elim
  · exact absurd hD (noAutDatum_of_O8m hbd e c L 𝒟)
  · exact absurd hD (noAutDatum_of_L44 e c L 𝒟)
  · exact (false_of_rankHyp_Sp6_four hX e).elim
  · exact (false_of_rankHyp_PSU5_two hX (by norm_num) e).elim
  · exact (false_of_rankHyp_PSU5_two hX (by norm_num) e).elim
  · exact (false_of_rankHyp_F4_two hX e).elim

end CFSG.RankThree.PartTwo.Sec19.SimsC198
