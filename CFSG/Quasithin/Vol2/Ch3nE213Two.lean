module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireE213
public import CFSG.Quasithin.Background.E2Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem Ch3n.e213TwoNonsolvable_of_member (hM : Ch3n.E213Member) : E2.E213TwoNonsolvable := by
  intro Γ _ _ H T M V h hchar hns
  obtain ⟨g, hg, hP, hcI, hIV, hrank⟩ := hM Γ H T M V h hchar hns
  obtain ⟨hAT, hAV, hAel, hcub, hnc, hAC⟩ := Ch3n.exists_cubic_of_pair hP hcI hIV
  refine ⟨g, hg, _, hAT.trans inf_le_left, ?_, hAel, hcub, hnc, ?_, Ch3n.count_of_pair hP hrank⟩
  · rw [Ch3n.cjSub_eq_conjSub]
    exact hAV
  · rw [Ch3n.cjSub_eq_conjSub]
    exact hAC

theorem E2.e213TwoStatement_holds
    : E2.E213TwoStatement :=
  E2.e213TwoStatement_of_nonsolvable
    (Ch3n.e213TwoNonsolvable_of_member Ch3E213M.Sp4C2.e213Member_holds)

end CFSG.Quasithin
