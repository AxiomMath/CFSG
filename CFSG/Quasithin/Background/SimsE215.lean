module

public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireE215

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.QuasithinUnique

namespace E215

theorem e215Nonsolvable_of_member (hM : Ch3n.E215Member) : E2.E215Nonsolvable := by
  intro Γ _ _ H T M V h hchar hTI hns
  obtain ⟨g, -, hP, hcI, hIV, hlt⟩ := hM Γ H T M V h hchar hTI hns
  obtain ⟨hAT, -, hAel, hcub, hAC, -⟩ := Ch3n.exists_cubic_of_pair hP hcI hIV
  have hAT' := hAT.trans inf_le_left
  exact E2.qhatOf_lt_two_of_cubic (hAT'.trans h.minParabolic.isSylow.1) (hAT'.trans h.normal_T)
    hAel hcub hAC hlt

end E215

theorem e215_qhat
    {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (hc : CharTwo H) (hTI : IsTISetIn V M) :
    qhatOf (autI h.elem H) < ((2 : ℚ) : WithTop ℚ) :=
  E2.e215Statement_of_nonsolvable (E215.e215Nonsolvable_of_member Ch3E213M.Sp4C2.e215Member_holds)
    Γ H T M V h hc hTI

end CFSG.Quasithin.SimsE2
