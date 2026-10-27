module

public import CFSG.Quasithin.EmptyFaithful.S1421QNSDefs
public import CFSG.Quasithin.EmptyFaithful.S1421QA5Fix
public import CFSG.Quasithin.EmptyFaithful.S1421QA5Count

public section

namespace CFSG.Quasithin

theorem autQ8D8Facts_holds : AutQ8D8Facts := by
  intro Q _ _ hQ
  have hcard : Nat.card Q = 32 := hQ.1
  exact ⟨AutQ8D8.not_seven_dvd_card_mulAut hcard hQ.card_sq_eq_one,
    AutQ8D8.not_seventeen_dvd_card_mulAut hcard,
    AutQ8D8.not_exists_subgroup_card_twentyFive hcard⟩

end CFSG.Quasithin
