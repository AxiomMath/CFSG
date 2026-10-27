module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocV
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4Va_le_centralizer_d4t : d4Va σ ≤ Subgroup.centralizer {d4t K σ} :=
  (Subgroup.closure_le _).2 (by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (commute_d4x₅_d4x₄ σ c 1).eq
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (commute_d4x₄_d4x₆ σ 1 c).eq.symm)

include hσ in
theorem VaC_le_cent : VaC σ ≤ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) := fun _ hv =>
  Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ]
    exact Subgroup.mem_centralizer_singleton_iff.1
      (d4Va_le_centralizer_d4t σ ((mem_VaC σ).1 hv))))

end CFSG.Quasithin.H13.F431.D4q.StdLoc
