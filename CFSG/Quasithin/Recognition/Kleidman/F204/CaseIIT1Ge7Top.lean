module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7I
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7L
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Reduce
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Top
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7J

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

theorem caseIIT1Ge7_holds : CaseIIT1Ge7 := by
  intro G _ _ L1 L2 S D X F hT1 α β α' hc hII hb7
  obtain ⟨μ, hμ, hμβ⟩ := exists_mu_not_le F hT1 hc hII
  exact caseII_T1_false_ge7_mu F hT1 hc hII hb7
    (fun x hx d hd d' hd' hne => Zv_inf_Zv_eq_bot_T1 F hT1 hx hd hd' hne) hμ hμβ

theorem caseIIT1_holds : CaseIIT1 := caseIIT1_of_ge7 caseIIT1Ge7_holds

theorem input15204F112Untw_holds : CFSG.Quasithin.He9.Input15204F112Untw :=
  input15204F112Untw_of_caseIIT1 caseIIT1_holds

end CFSG.Quasithin.Kleidman.F204
