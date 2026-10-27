module

public import CFSG.Quasithin.Background.E2Dihedral
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs3

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem inputE213Solvable_holds : InputE213Solvable := by
  intro Γ _ _ H T M V h hsolv _ hchar hVT hTV hV _ hVJ
  obtain ⟨-, -, A, hAT, -, hAel, hcub, hAV, -, hcount⟩ :=
    E2_13_two_of_isSolvable h hsolv hchar hVT hTV hV hVJ
  exact ⟨A, hAT, hAel, hcub, hAV, hcount⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
