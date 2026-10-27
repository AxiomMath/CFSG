module

public import CFSG.Quasithin.Vol2.Ch3n316
public import CFSG.Quasithin.Vol2.Ch3g316Red
public import CFSG.Quasithin.Vol2.Ch3g316E23

public section

namespace CFSG.Quasithin.Ch3g316

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem gen316_proved (hB1 : B69One) (he23 : E2.E23Nonsolvable) : Gen316 := by
  intro G _ _ H T M₂ R U hmp hsq hchar hns hRT hTR hJR hJH hQn hUe hUn hUQ hUC hK
  obtain ⟨hred, hJV⟩ := exists_reducedModule hB1 hmp ⟨hsq.2, hsq.1⟩ hRT hTR hJR hJH hQn hUe hUn
    hUQ hUC hK
  have hKQ := commutator_twoResidual_pCoreOf_le hmp hRT hTR hJR hJH hQn
  refine gen316_of_gen hmp hns hRT hTR hJR hKQ hQn ?_
  intro D hDP hDN hC hD
  exact e23_gen he23 hmp hsq hchar hred hJV hns hDP hDN hC hD

end CFSG.Quasithin.Ch3g316
