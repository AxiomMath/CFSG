module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

theorem phanEModels : PhanEModels := fun K _ _ f _ hK hq =>
  ⟨phanModelsRank2 K f hK hq, phanModelsRank3 K f hK hq⟩

section Certified


theorem phanELocal_of_classified (cfg : PhanEConfigChoice) (h1 : PhanEClassified cfg) :
    PhanELocal cfg :=
  phanELocal_of_parts cfg h1 phanEModels

end Certified

end CFSG.ClassicalInvolution.Phan.PhanE

end
