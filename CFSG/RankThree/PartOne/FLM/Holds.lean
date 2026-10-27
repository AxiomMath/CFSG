module

public import CFSG.RankThree.PartOne.FLM.Model
public import CFSG.RankThree.PartOne.MB3.FieldLmDefs

public section

namespace CFSG.RankThree.PartOne.FLM


theorem fieldLmModel_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    MB3.FieldLmModel := by
  intro G _ _ c K m hm hK _ hind hmod
  exact field_lm_model_aux hGA c K hm hK hind hmod

end CFSG.RankThree.PartOne.FLM
