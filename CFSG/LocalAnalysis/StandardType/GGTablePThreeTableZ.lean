module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZSc
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZCover

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

theorem twE6A2CentreInputTwo_holds :
    TwE6A2CentreInputTwo := by
  intro lab hlab htag hn
  rw [hn]
  exact labelAll_twE6A2CentreCont_of_sc le_rfl (by norm_num)
    (fun K _ _ σ hK hσ => twE6ScTableZ_holds K σ le_rfl hK hσ (by norm_num)) lab hlab htag hn

theorem twE6A2CentreInput_holds :
    TwE6A2CentreInput := by
  intro lab hlab htag hn3 h3
  exact labelAll_twE6A2CentreCont_of_sc (by omega) h3
    (fun K _ _ σ hK hσ => twE6ScTableZ_holds K σ (by omega) hK hσ h3) lab hlab htag rfl

end CFSG.StandardType.TablePThreeKG

end
