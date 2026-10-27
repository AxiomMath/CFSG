module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListSpDTwD
public import CFSG.LocalAnalysis.StandardType.GGF4H4ListSpBC

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4H4ListSp_holds :
    GGF4H4ListSp := by
  intro G _ _ p B Bs x L D J ks hres hB K hK lab hΛ htag hlab
  rcases htag with h | h | h | h
  · exact ggF4H4ListSp_BC G p B Bs x L D J ks hres hB K hK lab hΛ (Or.inl h) hlab
  · exact ggF4H4ListSp_BC G p B Bs x L D J ks hres hB K hK lab hΛ (Or.inr h) hlab
  · exact F4H4Sp.nbrList_of_DtwD hres hB hK hΛ (Or.inl h) hlab
  · exact F4H4Sp.nbrList_of_DtwD hres hB hK hΛ (Or.inr h) hlab

end CFSG.StandardType

end
