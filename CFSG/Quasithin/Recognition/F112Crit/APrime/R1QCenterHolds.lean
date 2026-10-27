module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.ConcreteA
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758Two
public import CFSG.Quasithin.Recognition.F112Crit.R1QPlusRed
public import CFSG.Quasithin.Recognition.Stroth.BenderH7

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112Crit

theorem r1QCenter_holds :
    R1QCenter := by
  intro G _ _ L1 L2 S hH hS3 hS hBig hnL2 hc
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hH.1
  rw [← P₂_swap_eq L2 L1 S] at hc
  exact (configA_of_le_omegaOneCenterOf hR hS3 hS hBig hnL2 hc le_rfl
    (Stroth.omegaOneCenterOf_ne_bot_of_hyp111 hH.1)).false

end CFSG.Quasithin.F112Crit.APrime

end
