module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSympLinAux2
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrTableBWeylTypeNonSplitOn_sympLin :
    GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitSympLinLabel := by
  rintro p hp hp2 lab hlab hS -
  apply nbrC_labelAll_guard
  rcases hS with ⟨ht, -, hpd⟩ | ⟨ht, -, hn, rfl⟩ | ⟨ht, -, hn, rfl⟩
  · exact ggWTB2_largeEvenLabelAll_weylTypeW_spNonsplit hp hlab ⟨ht, hpd⟩
  · exact ggWTB2_largeEvenLabelAll_weylTypeW_linearNs hp hlab ⟨ht, by rw [hn]; norm_num⟩
  · exact ggWTB2_largeEvenLabelAll_weylTypeW_linearNs hp hlab ⟨ht, by rw [hn]; norm_num⟩

end CFSG.StandardType

end
