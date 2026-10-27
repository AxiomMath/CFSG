module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FCompDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRowsSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRowsSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRowsOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNonthinAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOld
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtM22
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtL34
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_nonthinFixHalfRows_holds :
    K_NonthinFixHalfRows := by
  refine ⟨?_, ?_⟩
  · intro X _ _ hX2 L hqs hnt hsum
    obtain ⟨k, -, n, h | h | h | h | h⟩ := hsum
    · exact s16nt_sum_sl hX2 hqs hnt h
    · exact s16nt_sum_sp hX2 hqs hnt h
    · exact s16nt_sum_omPlus hX2 hqs hnt h
    · exact s16nt_sum_omMinus hX2 hqs hnt h
    · exact s16nt_row_alt_sum hX2 hqs h.1 h.2
  · intro X _ _ hX2 L m hqs hnt hirr h
    rcases h with ⟨n, h | h | h | h⟩ | ⟨n, h | h | h | h | h⟩ | h | h | h | ⟨n, h⟩ | h | h | h |
      h | h | h
    · exact s16nt_irr_sl hX2 hqs hnt hirr h
    · exact s16nt_irr_sp hX2 hqs hnt hirr h
    · exact s16nt_irr_omPlus hX2 hqs hnt hirr h
    · exact s16nt_irr_omMinus hX2 hqs hnt hirr h
    · exact s16nt_irr_sl hX2 hqs hnt hirr h
    · exact s16nt_irr_sp hX2 hqs hnt hirr h
    · exact s16nt_irr_omPlus hX2 hqs hnt hirr h
    · exact s16nt_irr_omMinus hX2 hqs hnt hirr h
    · exact s16nt_irr_su hX2 hqs hnt hirr h
    · exact s16nt_row_g2 hX2 hirr.1 inf_le_right h
    · exact s16nt_row_a6 hX2 hirr.1 inf_le_right h
    · exact s16nt_row_u43 hX2 hirr h
    · exact s16nt_row_alt_irr hX2 hqs hirr h.1 h.2
    · exact s16nt_row_a7 hX2 hirr.1 inf_le_right h
    · exact s16nt_row_sp6 hX2 hirr h
    · exact s16nt_row_l52 hX2 hirr h
    · exact s16nt_row_m22 hX2 hirr h
    · exact s16nt_row_l34 hX2 hirr h
    · exact (s16nt_irr_l32 hnt h.1).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
