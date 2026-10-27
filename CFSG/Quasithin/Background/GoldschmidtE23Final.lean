module

public import CFSG.Quasithin.Background.GoldschmidtE23Main
public import CFSG.Quasithin.Background.GoldschmidtE23Sym

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace GE23

section Final

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)

theorem e23Concl_of_nonsolvable (hP4 : AsB15Part4)
    (hComp : B69.AsB69Component) (hone : B69One) (h22 : E2.E22StatementNoN)
    (h : MinParabolic H T M) (hsq : SQTKGroup ↥H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)) (hns : ¬ Group.IsSolvable ↥H) :
    E2.E23Concl H T V hV :=
  e23Concl_of_three hV hP4 hComp hone h22 h hsq hred hJ hns fun hA5 =>
    e23_three_sym hV hP4 hComp hone h22 h hsq hred hJ hns hA5

end Final

theorem e23Nonsolvable_of_inputs (hP4 : AsB15Part4)
    (hComp : B69.AsB69Component) (hOne : B69One) (h22 : E2.E22StatementNoN) :
    E2.E23Nonsolvable := by
  intro Γ _ _ H T M V hV h hsq _ hred hJ hns
  exact e23Concl_of_nonsolvable hV hP4 hComp hOne h22 h hsq hred hJ hns

end GE23

end CFSG.Quasithin
