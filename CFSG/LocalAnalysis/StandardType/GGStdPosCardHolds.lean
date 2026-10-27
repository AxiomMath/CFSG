module

public import CFSG.LocalAnalysis.StandardType.GGStdPosCardDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosCardScalar
public import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
public import CFSG.LocalAnalysis.StandardType.GGRankOneTags

public section

namespace CFSG.StandardType

theorem ggKGPosCardStmt_holds :
    GGKGPosCardStmt := by
  intro G _ _ p Bs X t n f ψ hloc hstd
  obtain ⟨⟨hp, -, hadm, hrank⟩, ⟨hker, hrange, ht, -⟩, ⟨hel, -, -⟩, -, -⟩ := hloc
  obtain ⟨hdiv, ⟨nn, H, hct, -, -⟩, -⟩ := ggStdPos_bruhatData hrank ht
  obtain ⟨x, C, O, hE, hlin⟩ := ggRankOneModel_of_tag ht hadm hrank
  subst hrange
  exact ggStdPos_card_le_pow_rank_mul hct hdiv hE hlin ψ hker hp.ne_zero hstd hel.2

end CFSG.StandardType

end
